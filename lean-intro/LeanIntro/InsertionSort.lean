import Mathlib.Order.Basic
import LeanIntro.Macros

namespace InsertionSort

inductive Perm {α : Type} : List α -> List α -> Prop where
  | nil                         : Perm [] []
  | cons (x : α) (s t : List α) : Perm s t -> Perm (x :: s) (x :: t)
  | swap (x y : α) (s : List α) : Perm (x :: y :: s) (y :: x :: s)
  | trans (s t u : List α)      : Perm s t -> Perm t u -> Perm s u

theorem Perm.reflexivity {α : Type} (s : List α) :
  Perm s s := by
  induction s with
  | nil         => exact Perm.nil
  | cons x s ih => exact Perm.cons x s s ih

theorem Perm.symmetry {α : Type} (s t : List α) :
  Perm s t -> Perm t s := by
  intro h
  -- h: Perm s t
  induction h with
  | nil                      => exact Perm.nil
  | cons x s t _ ih          => exact Perm.cons x t s ih
  | swap x y s               => exact Perm.swap y x s
  | trans s t u _ _ ih₁ ih₂  => exact Perm.trans u t s ih₂ ih₁


