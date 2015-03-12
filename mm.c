/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * 
 *
 *
 * ************** Code Description *****************
 * 
 * Dynamic memory allocator.
 * We will use explicit list to keep track of the memory.
 * We will keep track of both free blocks and allocated blocks.
 * Each block will contain a header and a footer.
 *
 * The header will include informations about if the block is allocated 
 * or not giving it the value 1 if it is allocated or 0 if not.
 * It will also include information about the size of the block.
 *
 * The footer will serve the same purpose as the header and store the same 
 * information at the end of the block. This information can be used to 
 * navigate the list backwards and will be used in the Coalesce function.
 *
 * The Coalesce function is used to merge two free blocks aligned side by 
 * side to keep track of the real free space instead of spliced sizes.
 * example:   [ 4 |  |  |  | 4 |  |  |  | 4 |  |  |  | 2 |  | 2 |  ]
 *              free         alloc        free         free   alloc
 * malloc(5)
 *            this cannot happen unless we call the coalesce function before 
 *            to merge the two free aligning blocks.
 *
 * We will use the First fit method to allocate the memory to best fit the 
 * external fragmentation. This will result in a bit slower memory allocation 
 * but better fragmented and therefore better utilised allocation. This method 
 * runs trough the entire heap each time a malloc is performed, and tries to 
 * find the free block of the size closest to the memory size that is being 
 * allocated.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * === User information ===
 * Group: The_lone_riders
 * User 1: sigurdura13
 * SSN: 201192-2189
 * User 2: hafthort12
 * SSN: 220492-2819
 * === End User Information ===
 ********************************************************/
team_t team = {
    /* Group name */
    "the_lone_riders",
    /* First member's full name */
    "Sigurður Már Atlason",
    /* First member's email address */
    "sigurdura13@ru.is",
    /* Second member's full name (leave blank if none) */
    "Hafþór Snær Þórsson",
    /* Second member's email address (leave blank if none) */
    "hafthort12@ru.is",
    /* Leave blank */
    "",
    /* Leave blank */
    ""
};

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) = 4096 byte = 4GB */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define MINSIZE     16      /* Minumum block size - header + footer + prev free + next free */

#define MAX(x, y) ((x) > (y)? (x) : (y))  /* MAXimum comparison */
#define MIN(x, y) ((x) < (y)? (x) : (y))  /* Minimum comparison */ 

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */
static char *free_listp;  /* pointer to first free block */

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 
 * mm_init - initialize the malloc package.
 *
 * In this function we will initialize the heap at the beginning and 
 * initialize all global variables and call all necessary initializations, 
 * the function returns -1 if this fails. 
 */
int mm_init(void)
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL) {
        return -1;
    }

    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header - WZISE = padding */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;
    free_listp = heap_listp + DSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 *
 * This function is the main function behind this project.
 * when a program calls malloc it accepts size parameter 
 * and will return a pointer to a block in the heap of 
 * at least size, size. 
 * will not override or overlap any exsisting chunk of 
 * allocated memmory.
 * if no free space is available on the heap this 
 * function will return null.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 *
 * In this function we will free/deallocate a chunk of 
 * memmory pointed to by the ptr.
 * It will not return anything and will only work if
 * the ptr was returned using malloc or realloc and has
 * not been freed yet. 
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * when a program needs more memmory than it previosly requested
 * using malloc this function will be called.
 *
 * Here it is important to check if the added memmory is available
 * right behind the current location of the memmory and then the 
 * realloc will only return the pointer again and update the books 
 * to make sure it wont be overritten. Otherwise a expensive method
 * to copy the current memmory blocks to a new location with added 
 * memmory will be called.
 * If possible fit the memmory in gaps in current heap space, 
 * otherwise the heap needs to be expanded.
 * 
 * If ptr = null it is equalent to calling malloc
 * 
 * If size = 0 it is equalent to calling free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newPtr = ptr;
    size_t prevSize; /* Current size of the block to be changed */
    size_t asize;    /* Our calculated size of how big the block actually needs to be with header, footer, etc..  */

    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    } else {
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    if (size <= 0) {
        mm_free(ptr);
        return 0;
    }

    prevSize = GET_SIZE(HDRP(ptr));

    if (prevSize == asize) {
        return ptr;
    }    

    /* we are at the end of the heap */
    if (!GET_SIZE(HDRP(ptr))) {
        /* We extend the heap and extend the old block to the new heap size */
        size_t extendSize = MAX(asize, CHUNKSIZE);

        newPtr = extend_heap(extendSize/WSIZE);
        if (newPtr == NULL) {
            return NULL;
        }
        size_t newSize = extendSize + GET_SIZE(HDRP(ptr)) - asize;

        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        //removeFree(ptr);
        void *tmpPtr = NEXT_BLKP(ptr);
        PUT(HDRP(tmpPtr), PACK(newSize, 0));
        PUT(FTRP(tmpPtr), PACK(newSize, 0));

        // printf("After realloc\n");
        //mm_checkheap(VERBOSE);
        return ptr;
    } 

    /* The next block is free - we try to extend to it*/
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) {
        newPtr = NEXT_BLKP(ptr);
        size_t newTotalSize = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(newPtr));

        if (newTotalSize >= asize)
        {
            size_t newSize = newTotalSize - asize;

            if (newSize < MINSIZE) {
                PUT(HDRP(ptr), PACK(newTotalSize, 1));
                PUT(FTRP(ptr), PACK(newTotalSize, 1));
                //removeFree(ptr);

                // printf("After realloc\n");
                //mm_checkheap(VERBOSE);

                return ptr;    
            }
            else {
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                //removeFree(ptr);
                void *tmpPtr = NEXT_BLKP(ptr);
                PUT(HDRP(tmpPtr), PACK(newSize, 0));
                PUT(FTRP(tmpPtr), PACK(newSize, 0));

                // printf("After realloc\n");
                //mm_checkheap(VERBOSE);

                return ptr;
            }
        } else if (!GET_SIZE(HDRP(newPtr))) {
            size_t extendSize = MAX(asize, CHUNKSIZE);
            extend_heap(extendSize/WSIZE);
            size_t newSize = extendSize + newTotalSize - asize;

            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            //removeFree(ptr);
            void *tmpPtr = NEXT_BLKP(ptr);
            PUT(HDRP(tmpPtr), PACK(newSize, 0));
            PUT(FTRP(tmpPtr), PACK(newSize, 0));

            //printf("After realloc\n");
            //mm_checkheap(VERBOSE);
            
            return ptr;
        }
    }

    newPtr = mm_malloc(size);

    memcpy(newPtr, ptr, (GET_SIZE(HDRP(ptr))));
    mm_free(ptr);

    //printf("After realloc\n");
    //mm_checkheap(VERBOSE);

    return newPtr;
}


/* 
 *Coalesce will "merge" two or three blocks of memory that lie together
 * This is for the malloc to see how much memory really is available to
 * allocate new memory.
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 - both */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }
     
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* no fit */
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
        
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */
