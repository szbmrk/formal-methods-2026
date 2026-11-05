import LeanIntro.Macros

def cat {α : Type} (s t : List α) : List α :=
  match s with
  | [] => t
  | x :: s => x :: cat s t

theorem cat.nil {α : Type} (t: List α) :
  cat [] t = t := rfl

theorem cat.cons {α : Type} (x : α) (s t : List α) :
  cat (x :: s) t = x :: cat s t := rfl

-- lean shouldn't help me, because we are learning
attribute [irreducible] cat

theorem CatNil {α : Type} (s : List α) :
  cat s [] = s := by
  induction s with
  | nil => calc
    cat [] [] = [] := cat.nil []
  | cons x s ih => calc
    cat (x :: s) []
      = x :: cat s [] := cat.cons x s []
    _ = x :: s        := at [1, 2] use ih

theorem CatAssoc {α : Type} (s t u : List α) :
  cat s (cat t u) = cat (cat s t) u := by
  induction s with
  | nil => calc
      cat [] (cat t u)
        = cat t u := cat.nil (cat t u)
      _ = cat (cat [] t) u := at [2, 1] use cat.nil t
  | cons x s ih => calc
      cat (x :: s) (cat t u)
        = x :: cat s (cat t u)   := cat.cons x s (cat t u)
      _ = x :: cat (cat s t) u   := at [1, 2] use ih
      _ = cat (x :: cat s t) u   := at [2] use cat.cons x (cat s t) u
      _ = cat (cat (x :: s) t) u := at [2, 1] use cat.cons x s t


-- prove: cat (rev' t) (rev' s) = rev' (cat s t)

def rev' { α : Type } : List α -> List α
  | [] => []
  | x :: s => cat (rev' s) [x]

theorem rev'.nil {α : Type} : rev' ([] : List α) = [] := rfl

theorem rev'.cons {α : Type} (x : α) (s : List α) :
  rev' (x :: s) = cat (rev' s) [x] := rfl

theorem CatRev {α : Type} (s t : List α) :
  cat (rev' t) (rev' s) = rev' (cat s t) := by
  induction s with
  | nil => calc
      cat (rev' t) (rev' [])
        = cat (rev' t) [] := at [1, 2] use rev'.nil
      _ = rev' t          := at [1] use CatNil (rev' t)
      _ = rev' (cat [] t) := at [2, 1] use cat.nil t
  | cons x s ih => calc
      cat (rev' t) (rev' (x :: s))
        = cat (rev' t) (cat (rev' s) [x]) := at [1, 2] use rev'.cons x s
      _ = cat (cat (rev' t) (rev' s)) [x] := at [1] use CatAssoc (rev' t) (rev' s) [x]
      _ = cat (rev' (cat s t)) [x]        := at [1, 1] use ih
      _ = rev' (x :: cat s t)             := at [2] use rev'.cons x (cat s t)
      _ = rev' (cat (x :: s) t)           := at [2, 1] use cat.cons x s t


theorem RevInv {α : Type} (s : List α) :
  rev' (rev' s) = s := by
  induction s with
  | nil => calc
    rev' (rev' [])
      = rev' []   := at [1, 1] use rev'.nil
    _ = []        := at [1] use rev'.nil
  | cons x s ih => calc
    rev' (rev' (x :: s))
      = rev' (cat (rev' s) [x])                 := at [1, 1] use rev'.cons x s
    _ = cat (rev' [x]) (rev' (rev' s))          := at [2] use CatRev (rev' s) [x]
    _ = cat (cat (rev' []) [x]) (rev' (rev' s)) := at [1, 1] use rev'.cons x [] -- 4
    _ = cat (cat [] [x]) (rev' (rev' s))        := at [1, 1, 1] use rev'.nil -- 3
    _ = cat [x] (rev' (rev' s))                 := at [1, 1] use cat.nil [x] -- 1
    _ = x :: cat [] (rev' (rev' s))             := at [1] use cat.cons x [] (rev' (rev' (s))) -- 2
    _ = x :: rev' (rev' s)                      := at [1, 2] use cat.nil (rev' (rev' (s)))    -- 1
    _ = x :: s                                  := at [1, 2] use ih 

def rcat {α : Type} : List α -> List α -> List α
  | [], t => t
  | x :: s, t => rcat s (x :: t)

theorem rcat.nil {α : Type} (t : List α) :
  rcat [] t = t := rfl

theorem rcat.cons {α : Type} (x : α) (s t : List α) :
  rcat (x :: s) t = rcat s (x :: t) := rfl

def rev {α : Type} (s : List α) : List α :=
  rcat s []

theorem rev.def {α : Type} (s : List α) :
    rev s = rcat s [] := rfl

attribute [irreducible] rcat rev

-- prove rcat s t = cat (rev s) t

theorem RCat {α : Type} (s t : List α) :
    rcat s t = cat (rev s) t := by
    induction s generalizing t with
    | nil => calc
      rcat [] t
        = t                   := at [1] use rcat.nil t -- 5
      _ = cat [] t            := at [2] use cat.nil t -- 1
      _ = cat (rcat [] []) t  := at [2, 1] use rcat.nil [] -- 5
      _ = cat (rev []) t      := at [2, 1] use rev.def [] -- 7
    | cons x s ih => calc
      rcat (x :: s) t
        = rcat s (x :: t)             := at [1] use rcat.cons x s t
      _ = cat (rev s) (x :: t)        := at [1] use ih (x :: t)
      _ = cat (rev s) (x :: cat [] t) := at [2, 2, 2] use cat.nil t
      _ = cat (rev s) (cat [x] t)     := at [2, 2] use cat.cons x [] t
      _ = cat (cat (rev s) [x]) t     := at [1] use CatAssoc (rev s) [x] t
      _ = cat (rcat s [x]) t          := at [2, 1] use ih [x]
      _ = cat (rcat (x :: s) []) t    := at [2, 1] use rcat.cons x s []
      _ = cat (rev (x :: s)) t        := at [2, 1] use rev.def (x :: s)
