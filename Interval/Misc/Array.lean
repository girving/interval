import Batteries.Data.ByteArray
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend

/-!
## `Array` lemmas
-/

variable {α β : Type}

@[simp] lemma Array.getElem_map_fin (f : α → β) (x : Array α) {n : ℕ} (i : Fin n)
    (h : i < (x.map f).size) : (x.map f)[i]'h = f (x[i]'(by simpa using h)) := by
  simp only [Fin.getElem_fin, getElem_map]

lemma Array.getElem_eq_getElem! [Inhabited α] (d : Array α) {n : ℕ} (i : Fin n) (h : i < d.size) :
    d[i]'h = d[i]! := by
  simp only [Fin.getElem_fin, h, getElem!_pos]

@[simp] lemma Fin.getElem_fin' {Cont Elem : Type} {Dom : Cont → ℕ → Prop}
    [GetElem Cont Nat Elem Dom] (a : Cont) {n : ℕ} (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

/-!
## `ByteArray` lemmas
-/

@[simp] lemma ByteArray.size_mkEmpty (c : ℕ) : (ByteArray.emptyWithCapacity c).size = 0 := by
  simp only [ByteArray.size, ByteArray.emptyWithCapacity, List.size_toArray, List.length_nil]

lemma ByteArray.getElem_eq_data_getElem' (d : ByteArray) (i : Fin d.size) :
    d[i] = d.data[i] := by
  rfl

lemma ByteArray.getElem_eq_getElem! (d : ByteArray) (i : Fin d.size) : d[i] = d[i]! := by
  simp only [ByteArray.getElem_eq_data_getElem']
  exact Eq.symm (getElem!_pos d i (Fin.val_lt_of_le i (le_refl d.size)))

lemma ByteArray.getElemNat_eq_getElem! {d : ByteArray} {i : ℕ} (h : i < d.size) : d[i] = d[i]! := by
  exact Eq.symm (getElem!_pos d i h)

lemma ByteArray.getElem!_push (d : ByteArray) (c : UInt8) (i : ℕ) :
    (d.push c)[i]! = if i < d.size then d[i]! else if i = d.size then c else default := by
  split_ifs with lt e
  · have lt' : i < (d.push c).size := by simp only [ByteArray.size_push]; omega
    rw [← getElemNat_eq_getElem! lt, ← getElemNat_eq_getElem! lt', ByteArray.get_push_lt _ _ _ lt]
  · rw [e, ← getElemNat_eq_getElem!, ByteArray.get_push_eq]
  · apply getElem!_neg
    simp only [size_push, not_lt]
    omega

-- This is deprecated upstream, but the exact replacement is unclear
lemma Array.getElem?_eq_toList_get?' (a : Array α) (i : Nat) : a[i]? = a.toList[i]? := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg]

lemma ByteArray.getElem!_append (d0 d1 : ByteArray) (i : ℕ) :
    (d0 ++ d1)[i]! = if i < d0.size then d0[i]! else d1[i - d0.size]! := by
  by_cases i0 : i < d0.size
  · have g := ByteArray.get_append_left i0 (b := d1)
    simp only [getElemNat_eq_getElem!] at g
    simp only [g, i0, ↓reduceIte]
  · simp only [i0, ↓reduceIte]
    simp only [not_lt] at i0
    by_cases i1 : i < (d0 ++ d1).size
    · have g := ByteArray.get_append_right i0 i1
      simpa only [getElemNat_eq_getElem!] using g
    · simp only [not_lt, ByteArray.size_append] at i1
      rw [getElem!_neg, getElem!_neg]
      · omega
      · simp only [size_append]
        omega
