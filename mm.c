/*
 * mm.c
 * Leonardo Cervantes Lcervant
 * Segragated List Implementation of Malloc package Using Doubly-linked list
 * THis uses "Buckets" as way for storing block pointers of a certain length 
 * so that way malloc can always know where to look for a block. This malloc 
 * package uses 20 buckets and has a Chunk size of 1<<7. :D
 * The buckets themselves are store in a 2d array that is kept in a global 
 * variable segListp.
 * All If statements with VERBOSE are for debugging purposes only!
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

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<7)   /* Extend heap by this amount (bytes) */
#define MINIMUM     24      /* Minimum Size of block */
#define VERBOSE     0       /* For Debugging*/
#define BUCKETS     20      /* Buckets where we store the point*/

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
#define PUTNEXTFREEP(p, val)  (*(void **)(p + DSIZE) = val)
#define PUTPREVFREEP(p, val)  (*(void **)p = val)
#define GETNEXTFREEP(p) (*(void **)(p+ DSIZE))
#define GETPREVFREEP(p) (*(void **)p)


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static void *segListp = 0;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *ptr, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *ptr);
static void printblock(void *ptr);
static void checkheap(int lineno);
static void checkblock(void *ptr);
static void removeFreeBlock(void *ptr);
static void *putFirstFreeBlock(void *ptr);
static void checkFreeList(int lineno);
static int getBucketSize(unsigned int size);
void packagePtr(void *ptr, size_t size, unsigned int alloc);


/*
 * Initialize: return -1 on error, 0 on success.
 * Allocate enough space to store an adress in all the buckets as 
 * as out prolouge and epilougue. Malloc will start putting all 
 * fallocated and free blocks after the initial adresses of the 
 * buckets. Th extend_heap Function increases the heap past just
 * the bucket pointers and makes room for actual blocks
 */
int mm_init(void) {

    void *ptr;
    void **bucketList;
    int bucketSize;

    if (VERBOSE){
        printf("Initializing Heap!\n");
    }
    if ((segListp = mem_sbrk((BUCKETS * DSIZE) + 2*DSIZE)) == (void *)-1)
        return -1;
    heap_listp = (BUCKETS * DSIZE) + (char *)segListp;

    bucketList = (void **)segListp;
    for (bucketSize = 0; bucketSize < BUCKETS; bucketSize++){
        bucketList[bucketSize] = NULL;
    }

    /* Create the initial empty heap */

    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);
    
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((ptr = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
        return -1;
    return 0;
}

/*  Malloc - Takes a positive integer and returns a double aligned block that
 *  that is at least 24 bytes, If there is no heap , we initialize it and if 
 *  the requested block length is zero is is ignored. We then determine the 
 *  amount of block size that we need and look for it in free list using 
 *  find_fit. If there is a a block with the requireds size we return a 
 *  pointer and then allocate it using place. If there is not free block found 
 *  then we extend the heap and and place it to the appropriate pointer
 *
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *ptr;

    if (VERBOSE) {
        printf("\nCalled Malloc on size %d\n", (unsigned int)size);
        mm_checkheap(135);
    }
    
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
            printf("Exited Malloc with ptr %p\n\n\n", ptr);
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
    place(ptr, asize);
    if (VERBOSE){
            printf("Exited Malloc with ptr %p\n\n\n", ptr);
        }
    return ptr;
}

/* packagePtr - Used to pack the footer and header of a pointer
 */
void packagePtr(void *ptr, size_t size, unsigned int alloc)
{
    PUT(HDRP(ptr), PACK(size, alloc));
    PUT(FTRP(ptr), PACK(size, alloc));
}

/* free - When called, we un-allocated the pointer and then add it to the
 * begging of our buckets
 */
void free (void *ptr) {
    if (VERBOSE) {
        printf("\nCalled free on ptr %p\n", ptr);
        mm_checkheap(181);
    }
    
    if(!ptr) return;
    size_t size = GET_SIZE(HDRP(ptr));
    size_t alloc = 0;

    if (heap_listp == 0){
       mm_init();
    }

    packagePtr((void *)ptr, size, alloc);
    putFirstFreeBlock(ptr);
}

/*
 * place - Place block of asize bytes at start of free block ptr
 *         and split if remainder would be at least minimum block size
 * We always removed the block pointer from our buckets but is we split
 * up the block then the leftover block is put at the beginning of its 
 * repective bucket
 */
static void place(void *ptr, size_t asize)
{
    if (VERBOSE){
        printf("Called Place: %d block in ptr %p\n",(int)asize, ptr);
    }
    size_t csize = GET_SIZE(HDRP(ptr));

    if (VERBOSE){
        printf("Size of free block is %d\n", (int)csize);
    }

    removeFreeBlock(ptr);

    if ((csize - asize) >= (MINIMUM)) {
        /* Split the block since there is atleast 24 Bytes of unused space */
        packagePtr((void *)ptr, asize, 1);
        ptr = (int *)NEXT_BLKP(ptr);
        packagePtr((void *)ptr, (csize-asize), 0);
        putFirstFreeBlock(ptr);
    }
    else {
        /* Used the Entire Block */
        packagePtr((void *)ptr, csize, 1);
        
    }
}


/*
 * find_fit - Find a fit for a block with asize bytes
 * Searches through the each bucket staring with the smallest in which the
 * requested space will fit. If not free pointers are found the we search the 
 * next biggest bucket for a free block. We used a first fit search approach
 */
static void *find_fit(size_t asize)
{
    /* First fit search */
    void *ptr;
    int bucketSize;
    if (VERBOSE){
        printf("Called find_Fit for size %d\n",(int)asize);
    }

    bucketSize = getBucketSize(asize);
    for (int i = bucketSize; i < BUCKETS; i++){
        for(ptr = ((void **)segListp)[i]; ptr && GET_SIZE(HDRP(ptr));
            ptr = GETNEXTFREEP(ptr)) {
            if (asize <= GET_SIZE(HDRP(ptr))){
                return ptr;
            }
        }   
    }
    return NULL;
}
/* getBucketSize - We used to determine the bucket size that we want for 
 *  a requested amount of space. Since the blocks have to be minimum of 24
 *  blocks we start with a minum block size of 32 and double from that 
 */
static int getBucketSize(unsigned int size){
    size_t check;
    int bucket= 0;
    for (int i =5; i < 20 ; i++){
        check = 1<<i;
        if  (size<=check){
            return bucket;
        }
        bucket++;
    }   
    return bucket + 1;
}
/*  ExtendHeap - This is called at the beginning of malloc when there is no 
 *  heap or when there are no more free blocks with enough space to aloocate
 *  given amount of space. The ensuing free block that results fro mthis is 
 *  added to the beginning of the appropriate bucket
 */

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
    if (VERBOSE)
    {
        printf("Extended Heap By %d\n", (int)size);
    }

    /* Initialize free block header/footer and the epilogue header */
    packagePtr((void *)ptr, size, 0);
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 

    return putFirstFreeBlock(ptr);
}
/*  Coalesce - This is used to join adjacent free blocks when putFirstFree
 *  blockis called. There are 4 cases that may result  
 *  Case 1 - No adjacent free blocks, 
 *  Case 2 - next block is free, - remove that block and combine them
 *  Case 3 - the prev block is free - remove that block from the buckets
 *  Case 4 - Both adjacent blocks are free, remove both from the buckets 
 *  Since this is always called in putFirstFreeblock(), then pointer is always 
 *  added to the buckets with the the free adjacent free blocks
 */
static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (VERBOSE)
    {
        printf("Called Coalesce on ptr : %p\n", ptr);
    }
    if (prev_alloc && next_alloc) {            /* Case 1 */
        if (VERBOSE) {
            printf("Case 1\n");
        }
        return ptr;
    }

    else if (prev_alloc && !next_alloc) {                     /* Case 2 */
        if (VERBOSE) {
            printf("Case 2\n");
        }
        
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        removeFreeBlock(NEXT_BLKP(ptr));
        packagePtr((void *)ptr, size, 0);
    }

    else if (next_alloc && !prev_alloc) {                      /* Case 3 */
        if (VERBOSE) {
            printf("Case 3\n");
        }

        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        removeFreeBlock(PREV_BLKP(ptr));
        
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    else {                                     /* Case 4 */
        if (VERBOSE) {
            printf("Case 4\n");
        }
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
            GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        removeFreeBlock(NEXT_BLKP(ptr));
        removeFreeBlock(PREV_BLKP(ptr));

        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    return ptr;
}
/*  removeFreeBlock - Removes a block from the buckets, which implies that it
 *  it is either being merged with another free block or it is being allocated
 *  Wecheck is it is the the first block in its bucket class and also 
 *  adjust its prev and next pointers accordingly
 */

static void removeFreeBlock(void *ptr) {
    if (VERBOSE)
    {
        printf("Entered removeFreeBlock- Removing ptr : %p\n", ptr);
    }

    if (GETPREVFREEP(ptr)) {
        //Removing the Last free block
        PUTNEXTFREEP(GETPREVFREEP(ptr),GETNEXTFREEP(ptr));
    }
    if (GETNEXTFREEP(ptr)) {
        //Removing the First FREE Block
        PUTPREVFREEP(GETNEXTFREEP(ptr),GETPREVFREEP(ptr));
    } 

    int bucketSize = getBucketSize(GET_SIZE(HDRP(ptr)));
    if (ptr == ((void **)segListp)[bucketSize])
    {
        ((void **)segListp)[bucketSize] = GETNEXTFREEP(ptr);
    }
    PUTPREVFREEP(ptr, NULL);
    PUTNEXTFREEP(ptr, NULL);
    return;
}
/* putFirstFreeBlock - Takes a newly freed block, or goroup of adjacent
 * and put it in the front of its corresponding bucket. This always checks if 
 * there is any adjacent free blocks with Coalesce
 */

static void *putFirstFreeBlock(void *ptr){
    if (VERBOSE)
    {
        printf("Entered putFirstFreeBlock - Inserting ptr: %p ",ptr);
        printf("with Size %d\n",GET_SIZE(HDRP(ptr)));
    }
    ptr = coalesce(ptr);

    void *bucketList = ((void **)segListp)[getBucketSize(GET_SIZE(HDRP(ptr)))];
    if (!bucketList){
        PUTNEXTFREEP(ptr, NULL);
        PUTPREVFREEP(ptr, NULL);
    } else {
        PUTNEXTFREEP(ptr, bucketList);
        PUTPREVFREEP(bucketList, ptr);
        PUTPREVFREEP(ptr, NULL);
    } 
    ((void **)segListp)[getBucketSize(GET_SIZE(HDRP(ptr)))] = ptr;

    return ptr;
}

/*
 * realloc - Can be seen as free, malloc depending on its arguments
 * gets a new allocated block of new size, copies the data and frees the old
 * block!
 */
void *realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;
    if (VERBOSE){
        printf("Called Realloc on ptr %p to size %d\n", ptr, (unsigned int)size);
        mm_checkheap(417);
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
 * calloc - Malloc but everythoing is initialzed to 0
 */
void *calloc (size_t nmemb, size_t size) {
    if (VERBOSE){
        printf("Called Calloc for %d elements of size %d\n", (int)nmemb, (int)size);
        mm_checkheap(457);
    }
    void *ptr = malloc(nmemb * size);
    memset(ptr, 0,nmemb*size);
    return ptr;
}

/*
 * mm_checkheap - Makes sure that the Heap is is properly placed
 * Calls one helper to check the heap and the another checks the free list
 */
void mm_checkheap(int lineno) 
{    
    checkheap(lineno);
    checkFreeList(lineno);
}

void checkFreeList(int lineno) 
{
    if (VERBOSE)            
    {   
        printf("Checking the Free List . . . \n");
    }
    int bucket;
    void *block;
    for (bucket = 0; bucket < BUCKETS; bucket++){
        for (block = ((void **)segListp)[bucket];  block && 
            (GET_SIZE(HDRP(block))) > 0; block = GETNEXTFREEP(block)) 
        {
            printf("block %p, next%p\n", block, GETNEXTFREEP(block));
            if (GETNEXTFREEP(block) && GETPREVFREEP(GETNEXTFREEP(block)) != block){
                printf("Error prev and nex pointers\n");
                exit(1);
            }
            if (getBucketSize(GET_SIZE(HDRP(block))) != bucket){
                printf("Block %p is in the wront bucket\n", block);
                exit(1);
            }
        }
    }    
}



static void checkblock(void *ptr)
{
    if ((size_t)ptr % 8){
       printf("Error: %p is not doubleword aligned\n", ptr);
       exit(1);
    }
    if (GET(HDRP(ptr)) != GET(FTRP(ptr))){
       printf("Error: header does not match footer for ptr %p\n", ptr);
       printf("hdrp is %d, ftrp is %d\n",GET(HDRP(ptr)), GET(FTRP(ptr)));
       exit(1);
    }
}

/*
 * checkheap - Boss check of the heap for consistency
 */
void checkheap(int lineno)
{
    char *ptr = heap_listp;
    if (VERBOSE)
    {
        printf("\nHeap (%p):\n", heap_listp);
        printf("Called on Lineno %d\n",lineno);
    }   


    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
        if (VERBOSE)
        {
            printf("Bad prologue header\n");
        }
        exit(1);
    }
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

            printf("Checking Block ptr: %p, Alloc %d, Size %d\n", ptr, GET_ALLOC(HDRP(ptr)),GET_SIZE(HDRP(ptr)));
        }
        // printblock(ptr);
        checkblock(ptr);
    }
    if (VERBOSE){
    printf("Passed\n");
    }

    if ((GET_SIZE(HDRP(ptr)) != 0) || !(GET_ALLOC(HDRP(ptr)))){
        if (VERBOSE)
        {
            printf("Bad epilogue header\n");       
        }
        exit(1);
   }
   return;
}