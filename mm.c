/*
 * mm.c
 * Leonardo Cervantes Lcervant
 * NOTE TO STUDENTS: Replace this header comment with your own header
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define NEXT_FIT

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr ptr, compute address of its header and footer */
#define HDRP(ptr)       ((char *)(ptr) - WSIZE)
#define FTRP(ptr)       ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

/* Given block ptr ptr, compute address of next and previous blocks */
#define NEXT_BLKP(ptr)  ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE)))
#define PREV_BLKP(ptr)  ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE)))
#define PUTNEXTFREEP(p, val)  (*(unsigned int *)(p) = (val))
#define PUTPREVFREEP(p, val)  (*((unsigned int *)(p) + WSIZE) = (val))
#define GETNEXTFREEP(p) (*(unsigned int *)(p))
#define GETPREVFREEP(p) (*((unsigned int *)(p) + WSIZE))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static int *freeListStartp = 0;
static int *freeListEndp = 0;

#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *ptr, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *ptr);
static void printblock(void *ptr);
static void checkheap(int verbose);
static void checkblock(void *ptr);
void fixFreeList( void *ptr);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
     /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    void *ptr;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((ptr = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
        return -1;
    freeListStartp = (int *)ptr;
    freeListEndp = (int *)NEXT_BLKP(ptr);
    PUTNEXTFREEP(freeListStartp, freeListEndp);
    PUTPREVFREEP(freeListStartp, PREV_BLKP(freeListStartp));
    return 0;
}


void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *ptr;

    if (heap_listp == 0){
       mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)  return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((ptr = find_fit(asize)) != NULL) {
        place(ptr, asize);
        return ptr;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((ptr = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    fixFreeList((void *)ptr);
    place(ptr, asize);
    return ptr;
}

void fixFreeList( void *ptr) {
    int *freep;
    void *epilogue; 
    epilogue = NEXT_BLKP(ptr);
    for(freep = (int *) ptr; GETNEXTFREEP(freep) != freeListEndp; freep = GETNEXTFREEP(freep))
    {
        //Do nothing
    }
    PUTNEXTFREEP(freep, epilogue);
    freeListEndp = (int *)epilogue;
    PUTPREVFREEP(freeListStartp, ptr);
    PUTNEXTFREEP(ptr, freeListStartp);
    PUTPREVFREEP(ptr, heap_listp);
    freeListStartp = (int *)ptr;
    return;
}


void free (void *ptr) {

    if(!ptr) return;
    if(ptr == 0) return;


    size_t size = GET_SIZE(HDRP(ptr));

    if (heap_listp == 0){
       mm_init();
    }

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUTPREVFREEP(ptr,GETPREVFREEP(freeListStartp));
    PUTPREVFREEP(freeListStartp, ptr);
    PUTNEXTFREEP(ptr, freeListStartp);
    freeListStartp = (int *)ptr;
    coalesce(ptr);
}


static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) {            /* Case 1 */
    return ptr;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
    }

    else {                                     /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
        GET_SIZE(FTRP(NEXT_BLKP(ptr)));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
    }

#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)ptr) && (rover < NEXT_BLKP(ptr)))
    rover = ptr;
#endif

    return ptr;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    return NULL;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
}

static void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(ptr = mem_sbrk(size)) == -1)
    return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));         /* Free block header */
    PUT(FTRP(ptr), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(ptr);
}

/*
 * place - Place block of asize bytes at start of free block ptr
 *         and split if remainder would be at least minimum block size
 */
static void place(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));
    int * prevFree;
    int * nextFree;
    if ((csize - asize) >= (2*DSIZE)) {
        //Shrinks the current block
        prevFree = GETPREVFREEP(ptr);
        nextFree = GETNEXTFREEP(ptr);
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize-asize, 0));
        PUT(FTRP(ptr), PACK(csize-asize, 0));
        PUTNEXTFREEP(ptr, nextFree);
        PUTPREVFREEP(ptr, prevFree);
    }
    else {
        prevFree = GETPREVFREEP(ptr);
        nextFree = GETPREVFREEP(ptr);
        PUTNEXTFREEP(prevFree, nextFree);
        PUTPREVFREEP(nextFree, prevFree);
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    /* First fit search */
    void *ptr;

    for (ptr = (void *)freeListStartp; !GET_ALLOC(PTR) ; ptr = (void *)GETNEXTFREEP(ptr) ) {
        if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
            return ptr;
        }
    }
    return NULL;
}


// /*
//  * find_fit - Find a fit for a block with asize bytes
//  */
// static void *find_fit(size_t asize)
// {

// #ifdef NEXT_FIT
//     /* Next fit search */
//     char *oldrover = rover;

//     /* Search from the rover to the end of list */
//     for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
//     if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
//         return rover;

//     /* search from start of list to old rover */
//     for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
//     if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
//         return rover;

//     return NULL;  /* no fit found */
// #else
//     /* First fit search */
//     void *ptr;

//     for (ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)) {
//         if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
//             return ptr;
//         }
//     }
//     return NULL;
// #endif
// }

static void printblock(void *ptr)
{
    size_t hsize;//, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(ptr));
    // halloc = GET_ALLOC(HDRP(ptr));
    // fsize = GET_SIZE(FTRP(ptr));
    // falloc = GET_ALLOC(FTRP(ptr));

    if (hsize == 0) {
    printf("%p: EOL\n", ptr);
    return;
    }

 //      printf("%p: header: [%p:%c] footer: [%p:%c]\n", ptr,
    // hsize, (halloc ? 'a' : 'f'),
    // fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *ptr)
{
    if ((size_t)ptr % 8)
       printf("Error: %p is not doubleword aligned\n", ptr);
    if (GET(HDRP(ptr)) != GET(FTRP(ptr)))
       printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose)
{
    char *ptr = heap_listp;

    if (verbose)
    printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
       printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)) {
        if (verbose)
            printblock(ptr);
        checkblock(ptr);
    }

    if (verbose)
       printblock(ptr);
    if ((GET_SIZE(HDRP(ptr)) != 0) || !(GET_ALLOC(HDRP(ptr))))
       printf("Bad epilogue header\n");
}

