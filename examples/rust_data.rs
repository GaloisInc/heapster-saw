use std::collections::{HashMap, HashSet};

/* Test if a Result is Ok or Err */
pub fn test_result (r:&Result<u64,u64>) -> bool {
    match r {
        Ok(_) => true,
        Err(_) => false
    }
}

/* Sum of two types; yes, this is like Result, but defined locally so we can
 * make an impl block on it */
#[derive(Clone, Debug, PartialEq)]
pub enum Sum<X,Y> {
    Left (X),
    Right (Y)
}

/* Similar to above but in an impl block */
impl Sum<u64,u64> {
    pub fn test_sum_impl (&self) -> bool {
        match self {
            Sum::Left(_) => true,
            Sum::Right(_) => false
        }
    }
}

/* A linked list */
#[derive(Clone, Debug, PartialEq)]
#[repr(C,u64)]
pub enum List<X> {
    Nil,
    Cons (X,Box<List<X>>)
}

/* Test if a list is empty */
pub fn list_is_empty (l: &List<u64>) -> bool {
    match l {
        List::Nil => true,
        List::Cons (_,_) => false
    }
}

/* Get the head of a linked list or return an error */
pub fn list_head (l: &List<u64>) -> Box<Sum<u64,()>> {
    match l {
        List::Nil => Box::new(Sum::Right (())),
        List::Cons (x,_) => Box::new(Sum::Left (*x))
    }
}

/* Get the head of a linked list or return an error, in an impl block */
impl List<u64> {
    pub fn list_head_impl (&self) -> Result<u64,()> {
        match self {
            List::Nil => Err (()),
            List::Cons (x,_) => Ok (*x)
        }
    }
}
