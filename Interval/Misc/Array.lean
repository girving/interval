import Batteries.Data.ByteArray
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend

/-!
## `Array` lemmas
-/

variable {α β : Type}

@[simp] lemma Array.range_getElem (n k : ℕ) (kn : k < (range n).size) :
    ((Array.range n)[↑k]'kn) = k := by
  have nn : ∀ n, (Nat.fold n (fun b _ a ↦ push a b) #[]).size = n := by
    intro n; induction' n with n h
    · simp only [Nat.fold, size_toArray, List.length_nil, Nat.zero_eq]
    · simp only [Nat.fold, size_push, h]
  induction' n with n h
  · simp only [size, range, ofFn_zero, toList_toArray, List.length_nil, not_lt_zero'] at kn
  · simp only [Nat.fold, flip, Array.getElem_push, range] at kn h ⊢
    by_cases lt : k < size (Nat.fold n (fun b _ a => a.push b) #[])
    · simp only [size_ofFn, getElem_ofFn, implies_true, lt] at *
    · simp only [size_ofFn, getElem_ofFn] at kn ⊢

@[simp] lemma Array.getElem_map_fin (f : α → β) (x : Array α) {n : ℕ} (i : Fin n)
    (h : i < (x.map f).size) : (x.map f)[i]'h = f (x[i]'(by simpa using h)) := by
  simp only [Fin.getElem_fin, getElem_map]

lemma Array.getElem_eq_get! [Inhabited α] (d : Array α) {n : ℕ} (i : Fin n) (h : i < d.size) :
    d[i]'h = d.get! i := by
  simp only [Fin.getElem_fin, get!_eq_getElem?, get?, h, ↓reduceDIte, Option.getD_some]

@[simp] lemma Fin.getElem_fin' {Cont Elem : Type} {Dom : Cont → ℕ → Prop}
    [GetElem Cont Nat Elem Dom] (a : Cont) {n : ℕ} (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

/-!
## `ByteArray` lemmas
-/

@[simp] lemma ByteArray.size_mkEmpty (c : ℕ) : (ByteArray.mkEmpty c).size = 0 := by
  simp only [ByteArray.size, ByteArray.mkEmpty, Array.size_toArray, List.length_nil]

lemma ByteArray.getElem_eq_data_getElem' (d : ByteArray) (i : Fin d.size) :
    d[i] = d.data[i] := by
  rfl

lemma ByteArray.getElem_eq_get! (d : ByteArray) (i : Fin d.size) :
    d[i] = d.get! i := by
  simp only [ByteArray.get!, ByteArray.getElem_eq_data_getElem']
  rw [Array.get!_eq_getD, Array.getD]
  split_ifs with h
  · rfl
  · exfalso; exact h i.prop

lemma ByteArray.getElemNat_eq_get! (d : ByteArray) (i : ℕ) (h : i < d.size) :
    d[i] = d.get! i := by
  simp only [ByteArray.get!, ByteArray.getElem_eq_data_getElem']
  rw [Array.get!_eq_getD, Array.getD]
  split_ifs with b
  · rfl
  · exfalso; exact b h

lemma ByteArray.get!_push (d : ByteArray) (c : UInt8) (i : ℕ) :
    (d.push c).get! i = if i < d.size then d.get! i else if i = d.size then c else default := by
  split_ifs with lt e
  · have lt' : i < (d.push c).size := by simp only [ByteArray.size_push]; omega
    rw [←getElemNat_eq_get! _ _ lt', ←getElemNat_eq_get! _ _ lt, ByteArray.get_push_lt _ _ _ lt]
  · rw [e, ←getElemNat_eq_get!, ByteArray.get_push_eq]
  · simp only [not_lt] at lt
    simp only [ByteArray.get!, Array.get!, ByteArray.data_push, Array.getD_eq_get?, Array.get?,
      Array.size_push]
    rw [Array.getElem?_ge]
    · rfl
    · simp only [Array.size_push, ByteArray.size] at *; omega

-- This is deprecated upstream, but the exact replacement is unclear
lemma Array.getElem?_eq_toList_get?' (a : Array α) (i : Nat) : a[i]? = a.toList.get? i := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg, List.get?_eq_get, eq_comm]

lemma ByteArray.get!_eq_default (d : ByteArray) (i : ℕ) (le : d.size ≤ i) : d.get! i = default := by
  simp only [get!, Array.get!_eq_get?, Array.get?_eq_getElem?, Array.getElem?_eq_toList_get?',
    List.get?_eq_none le, Option.getD_none]

lemma ByteArray.get!_append (d0 d1 : ByteArray) (i : ℕ) :
    (d0 ++ d1).get! i = if i < d0.size then d0.get! i else d1.get! (i - d0.size) := by
  by_cases i0 : i < d0.size
  · have g := ByteArray.get_append_left i0 (b := d1)
    simp only [getElemNat_eq_get!] at g
    simp only [g, i0, ↓reduceIte]
  · simp only [i0, ↓reduceIte]
    simp only [not_lt] at i0
    by_cases i1 : i < (d0 ++ d1).size
    · have g := ByteArray.get_append_right i0 i1
      simpa only [getElemNat_eq_get!] using g
    · simp only [not_lt, ByteArray.size_append] at i1
      rw [ByteArray.get!_eq_default, ByteArray.get!_eq_default]
      · omega
      · simpa only [size_append]
