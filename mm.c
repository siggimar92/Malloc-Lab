/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
 * Group: The lone riders 
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* in this function we will initialize the heap at the beginning and 
     * initialize all global variables and call all necessary initializations, 
     * the function returns -1 if this fails. 
     */
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* this function is the main function behind this project.
     * when a program calls malloc it accepts size parameter 
     * and will return a pointer to a block in the heap of 
     * at least size, size. 
     * will not override or overlap any exsisting chunk of 
     * allocated memmory.
     * if no free space is available on the heap this 
     * function will return null.
     */

    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    /* in this function we will free/deallocate a chunk of 
     * memmory pointed to by the ptr.
     * It will not return anything and will only work if
     * the ptr was returned using malloc or realloc and has
     * not been freed yet. 
     */
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    /* when a program needs more memmory than it previosly requested
     * using malloc this function will be called.
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
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
