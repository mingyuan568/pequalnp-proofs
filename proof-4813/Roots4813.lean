import Pack4813
import MonotonePart

namespace PEqualNP.Outside.L_meta_4813
open Nine.Extended
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def featureA (u : Bool) : Word :=
  if u then rawCols.getD 0 0 &&& rawCols.getD 2 0 else 0

def ports (u : Bool) := rawCols ++ [featureA u]
def featureB (u : Bool) (ps : List (Fin 12)) :=
  nrm u ((ps.map (fun j => (ports u).getD j.val zero)).foldr (prime false) one)

def possibleB (u : Bool) :=
  let xs := List.ofFn (fun j : Fin 12 => (ports u).getD j.val zero)
  (([one] ++ xs ++ xs.flatMap (fun a => xs.map (fun b => prime false a b))).map (nrm u)).eraseDups

theorem feature_mem (u : Bool) (ps : List (Fin 12)) (h : ps.length≤2) :
    featureB u ps ∈ possibleB u := by
  simp only [featureB,possibleB,List.mem_eraseDups,List.mem_map]
  refine ⟨_,?_,rfl⟩
  have toOne (a : Word) : prime false a one=a := by exact BitVec.and_allOnes
  cases ps with
  | nil => simp
  | cons a ps =>
    cases ps with
    | nil =>
      simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,toOne]
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_ofFn.mpr ⟨a,rfl⟩
    | cons b ps =>
      cases ps with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,toOne]
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨_,List.mem_ofFn.mpr ⟨a,rfl⟩,
          List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨b,rfl⟩,rfl⟩⟩
      | cons _ _ => simp at h

theorem bank_normal (u : Bool) (ps : List (Fin 12)) :
    (makeBank u ps).map (nrm u) = rawCols ++ [featureA u, featureB u ps] := by
  have ha : nrm u (featureA u) = featureA u := nrm_id (by cases u <;> decide +kernel)
  have hr : rawCols.all plainWord = true := by decide +kernel
  simp only [makeBank,List.map_append,List.map_cons,List.map_nil, nrm_map hr]
  change (rawCols ++ [nrm u (featureA u)]) ++ [featureB u ps] = _
  rw [ha]
  simp

def changes (a : Word) (r s : TRow) := bit r a != bit s a

def needRaw (roots : List Word) (i : Fin 10) :=
  (List.range 10).any (fun w =>
    let lo := Fin.ofNat 1024 (1 <<< w)
    let hi := Fin.ofNat 1024 ((1 <<< w) ||| (1 <<< i.val))
    changes wordTarget lo hi && roots.all (fun x => x == xr i || !(changes x lo hi)))

def needsOK (u : Bool) (b : Word) :=
  (List.ofFn fun i : Fin 10 => needRaw (rawCols ++ [featureA u,b]) i).all id

theorem need_sound {u k S} (run : Live u wordTarget k S) {roots : List Word}
    (available : ∀ a∈S, a∈roots) (i : Fin 10) (h : needRaw roots i=true) : xr i∈S := by
  obtain ⟨w,_,hw⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,List.all_eq_true,changes,bne_iff_ne] at hw
  obtain ⟨a,ha,hd⟩ := live_row_difference run hw.1
  have only := hw.2 a (available a ha)
  by_cases eq : a=xr i
  · exact eq ▸ ha
  · simp [eq] at only
    exact (hd only).elim

def rootWords (u : Bool) (b : Word) (ka kb : Bool) :=
  (rawCols ++ (if ka && properB (featureA u) then [featureA u] else []) ++
    (if kb && properB b then [b] else [])).eraseDups

set_option maxRecDepth 16384 in
theorem select_root {u k S} (run : Live u wordTarget k S) (b : Word)
    (availability : ∀ a∈S, a∈rawCols ++ [featureA u,b])
    (witness : needsOK u b=true) :
    ∃ ka kb, (rootWords u b ka kb).toFinset=S := by
  classical
  have req : ∀ a∈rawCols, a∈S := by
    intro a ha
    have er : List.ofFn xr = rawCols := rfl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (er ▸ ha)
    apply need_sound run availability i
    exact List.all_eq_true.mp witness _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have good {a : Word} (ha : a∈S) : properB a=true := by
    have hp := live_proper run a ha
    simpa [properB,proper] using hp
  refine ⟨decide (featureA u∈S),decide (b∈S),?_⟩
  ext a
  simp only [List.mem_toFinset,rootWords,List.mem_eraseDups,List.mem_append]
  constructor
  · rintro ((h|h)|h)
    · exact req a h
    · split at h
      · next hk =>
        have eq := List.mem_singleton.mp h
        subst a
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hk).1
      · contradiction
    · split at h
      · next hk =>
        have eq := List.mem_singleton.mp h
        subst a
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hk).1
      · contradiction
  · intro ha
    have m := availability a ha
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h | h | h
    · exact Or.inl (Or.inl h)
    · subst a; simp [ha,good ha]
    · subst a; simp [ha,good ha]

def rootTest (s : Samples) (t : ProofTable) (k : Nat) (xs : List Word) :=
  (lookup s t k (keySet xs)).any (sameWords xs)

def rootChecks (u : Bool) (s : Samples) (t : ProofTable) (k : Nat) (b : Word) :=
  needsOK u b && [false,true].all (fun ka => [false,true].all (fun kb =>
    rootTest s t k (rootWords u b ka kb)))

theorem rootTest_sound {u s t k xs}
    (all : ∀ i<t.1 k, Impossible u wordTarget k (stateWords s t k i).toFinset)
    (ok : rootTest s t k xs=true) : Impossible u wordTarget k xs.toFinset := by
  obtain ⟨ys,hy,hs⟩ := List.any_eq_true.mp ok
  rw [sameWords_sound hs]
  have hm : ((t.2.2 k (keySet xs)).bind (fun code => if code/4<t.1 k then
      some (symWords (code%4) (stateWords s t k (code/4))) else none)) = some ys := by
    simpa [lookup] using hy
  obtain ⟨code,_,hh⟩ := Option.bind_eq_some_iff.mp hm
  split at hh
  · next h => cases hh; exact symWords_ok (all _ h) _
  · contradiction

theorem verdict {u k S s t cap} (ps : List (Fin 12)) (hps : ps.length≤2)
    (all : ∀ i<t.1 cap, Impossible u wordTarget cap (stateWords s t cap i).toFinset)
    (check : ∀ b ∈ possibleB u, rootChecks u s t cap b=true)
    (hk : k≤cap) (run : Live u wordTarget k S)
    (supply : ∀ a∈ S, a∈(makeBank u ps).map (nrm u)) : False := by
  let b := featureB u ps
  have tests := Bool.and_eq_true_iff.mp (check b (feature_mem u ps hps))
  obtain ⟨ka,kb,eq⟩ := select_root run b (fun a ha => by simpa only [bank_normal] using supply a ha) tests.1
  have mk (v : Bool) : v ∈ [false,true] := by cases v <;> simp
  have ok := List.all_eq_true.mp (List.all_eq_true.mp tests.2 ka (mk ka)) kb (mk kb)
  have no := rootTest_sound all ok
  rw [eq] at no
  exact no k hk run

end PEqualNP.Outside.L_meta_4813
