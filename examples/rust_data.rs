use std::collections::{HashMap, HashSet};

/* The logical and operation as a function on bool */
pub fn bool_and (x:bool, y:bool) -> bool {
    x & y
}

/* The logical and operation as a function on bools in a pair */
pub fn bool_and_pair (xy:(bool,bool)) -> bool {
    xy.0 & xy.1
}

#[repr(C)]
pub struct BoolStruct { fst_bool:bool,snd_bool:bool }

/* The logical and operation as a function on bools in a struct */
pub fn bool_and_struct (xy:BoolStruct) -> bool {
    xy.fst_bool & xy.snd_bool
}

/* A struct containing 4 32-bit values, to test how structs that fit into 2
 * 64-bit values are represented */
pub struct FourValues(u32,u32,u32,u32);

pub fn mk_four_values (x1:u32,x2:u32,x3:u32,x4:u32) -> FourValues {
    FourValues(x1,x2,x3,x4)
}

pub extern fn mk_four_values_extern (x1:u32,x2:u32,x3:u32,x4:u32) -> FourValues {
    FourValues(x1,x2,x3,x4)
}

pub fn four_values_proj1 (x:FourValues) -> u32 {
    match x {
        FourValues(x1,_,_,_) => x1
    }
}

pub extern fn four_values_proj1_extern (x:FourValues) -> u32 {
    match x {
        FourValues(x1,_,_,_) => x1
    }
}


/* A struct containing 5 32-bit values, to test how structs that do not quite
 * fit into 2 64-bit values are represented */
pub struct FiveValues(u32,u32,u32,u32,u32);

pub fn mk_five_values (x1:u32,x2:u32,x3:u32,x4:u32,x5:u32) -> FiveValues {
    FiveValues(x1,x2,x3,x4,x5)
}

pub extern fn mk_five_values_extern (x1:u32,x2:u32,x3:u32,x4:u32,x5:u32)
                                     -> FiveValues {
    FiveValues(x1,x2,x3,x4,x5)
}


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


/***
 *** Some tests for how Rust compiles functions on enums
 ***/

impl Sum<u64,u64> {
    pub fn test_sum_impl (&self) -> bool {
        match self {
            Sum::Left(_) => true,
            Sum::Right(_) => false
        }
    }

    pub fn mk_u64_sum_left (x:u64) -> Self {
        Sum::Left (x)
    }

    pub extern fn mk_u64_sum_left_extern (x:u64) -> Self {
        Sum::Left (x)
    }
}

pub fn mk_string_sum_left (x:&str) -> Sum<String,u64> {
    Sum::Left (x.to_string())
}

pub fn mk_sum_sum_left (x:Sum<u64,u64>) -> Sum<Sum<u64,u64>,u64> {
    Sum::Left (x)
}

pub extern fn mk_sum_sum_left_extern (x:Sum<u64,u64>) -> Sum<Sum<u64,u64>,u64> {
    Sum::Left (x)
}


/* A struct containing a string */
pub struct StrStruct(String);

impl StrStruct {
    /* Constructor for StrStruct */
    pub fn new(name: &str) -> StrStruct {
        StrStruct(name.to_string())
    }
    pub extern fn new_extern(name: &str) -> StrStruct {
        StrStruct(name.to_string())
    }

    /* Accessor for StrStruct */
    pub fn name(&self) -> String {
        match self {
            StrStruct(s) => s.to_string(),
        }
    }
    pub extern fn name_extern(&self) -> String {
        match self {
            StrStruct(s) => s.to_string(),
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
