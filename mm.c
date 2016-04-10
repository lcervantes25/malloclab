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
#include "contracts.h"
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
#define MINIMUM     24      /* Minimum Size of block */
#define VERBOSE     1       /* Debugging Purposes*/

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
#define PUTNEXTFREEP(p, val)  (*(unsigned long *)(p) = (val))
#define PUTPREVFREEP(p, val)  (*((unsigned long *)(p) + DSIZE) = (val))
#define GETNEXTFREEP(p) (*(unsigned long *)(p))
#define GETPREVFREEP(p) (*((unsigned long *)(p) + DSIZE))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static int *freeListStartp = 0;
static int *freeListEndp = 0;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *ptr, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *ptr);
static void printblock(void *ptr);
static void checkheap(int verbose);
static void checkblock(void *ptr);
static void fixFreeList( void *ptr);
static void removeFreeBlock(void *ptr);
static void putFirstFreeBlock(void *ptr);
static void checkFreeList(int lineno);
void *getLastFreep(void * ptr);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {

    if (VERBOSE){
        printf("Initializing Heap!\n");
    }
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
    freeListEndp = 0;
    PUTNEXTFREEP(freeListStartp, (long)freeListEndp);
    // PUTPREVFREEP(freeListStartp, (long)PREV_BLKP(freeListStartp));
    PUTPREVFREEP(freeListStartp, 0);
    return 0;
}


void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *ptr;

    if (VERBOSE) {
        printf("\nCalled Malloc on size %d\n", (unsigned int)size);
    }
    mm_checkheap(130);

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
    asize = MAX(asize, MINIMUM);
    if ((ptr = find_fit(asize)) != NULL) {
        place(ptr, asize);
        if (VERBOSE){
            printf("\nExited Malloc with ptr %p\n\n\n", ptr);
        }
        return ptr;
    }
    if (VERBOSE){
        printf("Did not Find Fit - Extending size\n");
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((ptr = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    if (VERBOSE){
        printf("Extended the heap by %d bytes and got ptr :%p\n",(int) extendsize, ptr);
    }
    // fixFreeList((void *)ptr);
    place(ptr, asize);
    if (VERBOSE){
            printf("\nExited Malloc with ptr %p\n\n\n", ptr);
        }
    return ptr;
}

static void fixFreeList( void *ptr) {
    int *freep, *oldFreeListStartp, *oldFreeListPrevp, *oldFreeListNextp;
    int * oldFreeListEnd;
    void *epilogue; 
    if (VERBOSE)
    {
        printf("\nCalled fixFreeList on ptr: %p\n", ptr);
    }
    if (freeListStartp == 0){
        return;
    }
    // if ((int *)getLastFreep(ptr) == freeListEndp){
    //     return;
    // }
    
    epilogue = NEXT_BLKP(ptr);

    oldFreeListEnd = freeListEndp;

    oldFreeListStartp = (int *)freeListStartp;
    oldFreeListPrevp = (int *)GETPREVFREEP(freeListStartp);
    oldFreeListNextp = (int *)GETNEXTFREEP(freeListStartp);

    freeListStartp = (int *)ptr;
    freeListEndp = (int *)epilogue;

    PUTNEXTFREEP(freeListStartp, (long)oldFreeListStartp);
    PUTPREVFREEP(freeListStartp, (long)oldFreeListPrevp);

    if (oldFreeListStartp == oldFreeListNextp){
        return;
    }

    if (VERBOSE)
    {
        printf("Right Before the loop\n");
    }
    for(freep = (int *)oldFreeListStartp; (int*)GETNEXTFREEP(freep) != oldFreeListEnd; freep = (int *)GETNEXTFREEP(freep))
    {
        // printf("current free ptr :%p\n", freep);
        // printf("next ptr is ptr %p:\n", (int*)GETNEXTFREEP(freep));
    }
    if (VERBOSE)
    {
        printf("rIGHT AFTER THE LOOP\n");
    }
    PUTNEXTFREEP(freep, (long)epilogue);
    PUTPREVFREEP(oldFreeListStartp, (long)ptr);
    return;
}


void free (void *ptr) {
    if (VERBOSE) {
        printf("\nCalled free on ptr %p\n", ptr);
    }
    if(!ptr) return;
    if(ptr == 0) return;


    size_t size = GET_SIZE(HDRP(ptr));

    if (heap_listp == 0){
       mm_init();
    }


    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    if (freeListStartp){
        PUTNEXTFREEP(ptr,(long)freeListStartp);
        PUTPREVFREEP(freeListStartp, (long)ptr); 
    } else{
        PUTNEXTFREEP(ptr, 0);
    }
    PUTPREVFREEP(ptr, 0);
    freeListStartp = (int *)ptr;

    printf("freeListStartp %p,next ptr %p \n", freeListStartp, (int *)GETNEXTFREEP(freeListStartp));

    mm_checkheap(251);
    coalesce(ptr);
}

/*
 * place - Place block of asize bytes at start of free block ptr
 *         and split if remainder would be at least minimum block size
 */
static void place(void *ptr, size_t asize)
{
    if (VERBOSE){
        printf("\nCalled Place: %d block in ptr %p\n",(int)asize, ptr);
    }
    size_t csize = GET_SIZE(HDRP(ptr));

    if (VERBOSE){
        printf("Size of free block is %d\n", (int)csize);
    }
    int * prevFree;
    int * nextFree;
    int * newptr;

    if ((csize - asize) >= (MINIMUM)) {
        //Shrinks the current block
        prevFree = (int *)GETPREVFREEP(ptr);
        nextFree = (int *)GETNEXTFREEP(ptr);

        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));

        newptr = (int *)NEXT_BLKP(ptr);
        PUT(HDRP(newptr), PACK(csize-asize, 0));
        PUT(FTRP(newptr), PACK(csize-asize, 0));

        PUTNEXTFREEP(newptr, (long)nextFree);
        PUTPREVFREEP(newptr, (long)prevFree);
        if ((int *)ptr == freeListStartp){
            freeListStartp = newptr;
        }
        if (prevFree){
            PUTNEXTFREEP(prevFree, (long)newptr);
        }
        if (nextFree){
            PUTPREVFREEP(nextFree, (long)newptr);
        }
        printf("freeListStartp %p, next %p, prev %p\n",freeListStartp, nextFree, prevFree);
    }
    else {
        prevFree = (int *)GETPREVFREEP(ptr);
        nextFree = (int *)GETNEXTFREEP(ptr);

        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
        if ((int *)ptr == freeListStartp){
            freeListStartp = nextFree;
        }
        if (prevFree){
            PUTNEXTFREEP(prevFree, (long)nextFree);
        }
        if (nextFree){
            PUTPREVFREEP(nextFree, (long)prevFree);
        }

        printf("freeListStartp %p, next %p, prev %p\n",freeListStartp, nextFree, prevFree);
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    /* First fit search */
    void *ptr;
    if (VERBOSE){
        printf("\nCalled find_Fit for size %d\n",(int)asize);
    }
    for (ptr = (void *)freeListStartp; ptr; ptr = (void *)GETNEXTFREEP(ptr) ) {
        if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
            return ptr;
        }
    }
    return NULL;
}
static void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;

    if (VERBOSE)
    {
        printf("Called Extend Heap\n");
    }
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(ptr = mem_sbrk(size)) == -1)
    return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));         /* Free block header */
    PUT(FTRP(ptr), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* New epilogue header */
    // fixFreeList(ptr);
    // putFirstFreeBlock(ptr);
    /* Coalesce if the previous block was free */
    return coalesce(ptr);

}

static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    // int *prevFree, *nextFree;
    int *freeptr;
    if (VERBOSE)
    {
        printf("\nCalled Coalesce on ptr : %p\n", ptr);
    }
    if (prev_alloc && next_alloc) {            /* Case 1 */
        if (VERBOSE)
        {
            printf("Case 1\n");
        }
        return ptr;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        if (VERBOSE)
        {
            printf("Case 2\n");
        }
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        freeptr = (int *)NEXT_BLKP(ptr);
        // prevFree = (int *)GETPREVFREEP(freeptr);
        // nextFree = (int *)GETNEXTFREEP(freeptr);
        removeFreeBlock(freeptr);
        removeFreeBlock(ptr);
        // removeFreeBlock(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size,0));
        putFirstFreeBlock(ptr);
        // if (freeptr == freeListStartp){
        //     freeListStartp = ptr;
        // }
        // if (prevFree){
        //     PUTNEXTFREEP(prevFree, (long)freeptr);
        // } else {
        //     PUTPREVFREEP(ptr, 0);
        // }
        // if (nextFree){
        //     PUTPREVFREEP(nextFree, (long)freeptr);
        // } else {
        //     PUTNEXTFREEP(ptr, 0);
        // }
        
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        if (VERBOSE)
        {
            printf("Case 3\n");
        }
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        freeptr = (int *)PREV_BLKP(ptr);
        removeFreeBlock(freeptr);
        removeFreeBlock(ptr);
        ptr = freeptr;
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        putFirstFreeBlock(ptr);
        // freeptr = (int *)ptr;
        // prevFree = (int *)GETPREVFREEP(freeptr);
        // nextFree = (int *)GETNEXTFREEP(freeptr);
        // ptr = PREV_BLKP(ptr);

        // PUT(HDRP(ptr), PACK(size, 0));
        // PUT(FTRP(ptr), PACK(size, 0));

        // if (freeptr == freeListStartp){
        //     freeListStartp = ptr;
        // }
        // if (prevFree){
        //     PUTNEXTFREEP(prevFree, (long)freeptr);
        // } else  {
        //     PUTPREVFREEP(ptr, 0);
        // }
        // if (nextFree){
        //     PUTPREVFREEP(nextFree, (long)freeptr);
        // } else {
        //     PUTNEXTFREEP(ptr, 0);
        // }
    }

    else {                                     /* Case 4 */
        if (VERBOSE)
        {
            printf("Case 4\n");
        }
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
            GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        removeFreeBlock(NEXT_BLKP(ptr));
        removeFreeBlock(PREV_BLKP(ptr));
        removeFreeBlock(ptr);
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
        putFirstFreeBlock(ptr);
    }

    return ptr;
}

static void removeFreeBlock(void *ptr) {
    int *prev;
    int *next;
    if (VERBOSE)
    {
        printf("\nEntered removeFreeBlock- Removing ptr : %p\n", ptr);
    }


    prev = (int *)GETPREVFREEP(ptr);
    next = (int *)GETNEXTFREEP(ptr);
    if (prev)
    {
        PUTNEXTFREEP(prev,(long)next);
    }
    if (next)
    {
    PUTPREVFREEP(next, (long)prev);
    }
    if ((int *)ptr == freeListStartp){
        freeListStartp = next;
    }
    printf("freeListStartp: %p, freeListEndp: %p\n", freeListStartp, freeListEndp);
    return;
}


static void putFirstFreeBlock(void *ptr){
    if (VERBOSE)
    {
        printf("\nEntered putFirstFreeBlock - Inserting : %p\n",ptr);
    }

    if (freeListStartp == 0)
    {
        freeListStartp = (int *)ptr;
        freeListEndp = 0;
        PUTNEXTFREEP(freeListStartp, (long)freeListEndp);
        PUTPREVFREEP(freeListStartp, 0);
        return;
    }

    if ((int *)ptr == freeListStartp)
    {
        if (VERBOSE)
        {
            printf("No Need to fix\n");
        }
        return;
    } 
    if (freeListStartp != freeListEndp){
        PUTPREVFREEP(freeListStartp, (long)ptr);
    }
    PUTNEXTFREEP(ptr, (long)freeListStartp);
    PUTPREVFREEP(ptr, 0);
    
    freeListStartp = (int *)ptr;
    return;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;
    if (VERBOSE){
        printf("Called Realloc on ptr %p to size %d\n", ptr, (unsigned int)size);
    }

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
    checkheap(lineno);
    checkFreeList(lineno);
}

void checkFreeList(int lineno) {
    
    int *ptr = freeListStartp;

    if (ptr == 0){
        if(VERBOSE){
        printf("No Free list Created yet\n");
        }
        return;
    }

    if (VERBOSE)
    {
        printf("Checking Free List .... (%p):\n", freeListStartp);
    }   

    if (freeListStartp == freeListEndp){
        if (VERBOSE){
            printf(" There is no Freelist .. .\n");
            printf("Passed!!\n");
        }
        return;
    }
    if (VERBOSE)
    {
        printf("CHecking Header Pointer...\n");
    }
    if (GET_ALLOC(HDRP(freeListStartp)) || ((int *)GETPREVFREEP(ptr) != 0))
    {   
        if (VERBOSE)
        {
            printf("Bad free list Start header / alloc and prev \n");
        }
        exit(1);
    }

    checkblock(freeListStartp);

    if(!(int *)GETNEXTFREEP(freeListStartp))
    {
        if (VERBOSE)
        {
            printf("There is only One free block . . .Passed!!\n");    
        }
        return;
    }
    if (VERBOSE)
    {
       printf("Checking Free list\n");
    }
    for (ptr = freeListStartp; (int *)ptr; ptr = (int *)GETNEXTFREEP(ptr)) {
        if (ptr == (int *)GETNEXTFREEP(ptr)){
            if (VERBOSE){
                printf("ERROR Infinite Loop: ptr %p, next:%p, End of List: %p\n",ptr, (int *)GETNEXTFREEP(ptr), (int *)freeListEndp );
            }
            exit(1);
        }
        if (VERBOSE){
            printf("ptr: %p, next ptr: %p\n",ptr, (int *)GETNEXTFREEP(ptr) );
        }
        checkblock(ptr);
    }
    if (VERBOSE)
    {
        printf("Done CHecking Free list\n");
    }
    
    // if (verbose)
    //    printblock(ptr);

    if (ptr != freeListEndp){
        if (VERBOSE){
            printf("Bad Free List End\n");
        }
        exit(1);
    }
    if (VERBOSE)
    {
        printf("Free List Okay!");
    }
}


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
    if ((size_t)ptr % 8){
       printf("Error: %p is not doubleword aligned\n", ptr);
       exit(1);
    }
    if (GET(HDRP(ptr)) != GET(FTRP(ptr))){
       printf("Error: header does not match footer\n");
       exit(1);
    }
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int lineno)
{
    char *ptr = heap_listp;
    if (VERBOSE)
    {
        printf("\nHeap (%p):\n", heap_listp);
        printf("Called on Lineno %d\n",lineno);
    }   


    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
       printf("Bad prologue header\n");
    if (VERBOSE){
    printf("Checking headlistp . . . ");
    }
    checkblock(heap_listp);
    if (VERBOSE){
    printf("Passed\n");
    } 
    if (VERBOSE){
    printf("Checking heap . . .\n");
    }
    for (ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)) {
        if(VERBOSE) {
            printf("Checking Block ptr: %p\n", ptr);
        }
        checkblock(ptr);
    }
    if (VERBOSE){
    printf("Passed\n");
    }

    // if (verbose)
    //    printblock(ptr);
    if ((GET_SIZE(HDRP(ptr)) != 0) || !(GET_ALLOC(HDRP(ptr))))
       printf("Bad epilogue header\n");
   return;
}

