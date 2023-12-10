module Data.Erased

public export
record Erased ty where
  constructor Erase
  0 value : ty
