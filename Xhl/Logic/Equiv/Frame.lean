import Xhl.Measures.Range
import Xhl.Language.Semantics

open Continuous

/-!
# Frame reasoning: what a command does not write, it does not change

`NoWrite x c` says that no assignment or sampling in `c` targets the name `x`.
`range_frame` is the frame property that follows: a command that does not write `x`
keeps the value of `x` inside any set it started in, almost surely, by structural
induction on the command (the `while` case by induction on the fuel approximants).
The predicate reads only the memory of the state, so a `release` is a Dirac step
like `skip`.

`range_seq_keep` is the form the case studies use: a first statement that leaves a
counter alone lets the range of the whole sequence be read off the second statement,
from the states that still carry the counter's original value.
-/

open MeasureTheory ProbabilityTheory ENNReal

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-! ## Frame: a statement that does not write a variable leaves it unchanged -/

/-- `NoWrite x c`: no assignment or sampling in `c` targets the name `x`. -/
def NoWrite (x : ident) : Cmd ident M → Prop
  | .abort => True
  | .skip => True
  | .assign y _ => y.name ≠ x
  | @Cmd.random _ _ _ y _ _ => y.name ≠ x
  | .cond _ c₁ c₂ => NoWrite x c₁ ∧ NoWrite x c₂
  | .seq c₁ c₂ => NoWrite x c₁ ∧ NoWrite x c₂
  | .while _ c => NoWrite x c
  | .release _ => True
  | .loc y c => y.name ≠ x ∧ NoWrite x c

/-- **Frame**: if `c` does not write `x` and the value of `x` lies in a set `S` (with a
    measurable preimage), then it still does after `c`, almost surely. -/
lemma range_frame {t : Ty} (x : ident) (S : Set t.interp)
    (hS : MeasurableSet {a : M.heap | M.get a t x ∈ S}) :
    ∀ c : Cmd ident M, NoWrite x c → ∀ s : St M, M.get s.1 t x ∈ S →
      range (fun s' : St M => M.get s'.1 t x ∈ S) (osemA c s) := by
  have hS' : MeasurableSet {s : St M | M.get s.1 t x ∈ S} := measurable_fst hS
  intro c
  induction c with
  | abort => intro _ s _; exact range_null _
  | skip => intro _ s hs; exact range_dirac _ s hS' hs
  | release e => intro _ s hs; exact range_dirac _ _ hS' hs
  | assign y e =>
    intro hw s hs
    refine range_dirac _ _ hS' ?_
    show M.get (M.set s.1 _ y.name (esem e s.1)) t x ∈ S
    rw [M.get_set_ne _ _ s.1 y.name x _ (Or.inr hw)]; exact hs
  | @random _ y κ _ =>
    intro hw s hs
    rw [osemA_random]
    refine range_bind (PA := fun _ => True) _ _ ?_ hS' (by simp [range]) (fun v _ => ?_)
    · exact (Measure.measurable_dirac).comp
        (((M_set_measurable (t := _) y.name).comp
          (measurable_const.prodMk measurable_id)).prodMk measurable_const)
    · refine range_dirac _ _ hS' ?_
      show M.get (M.set s.1 _ y.name v) t x ∈ S
      rw [M.get_set_ne _ _ s.1 y.name x _ (Or.inr hw)]; exact hs
  | cond e c₁ c₂ ih₁ ih₂ =>
    intro hw s hs
    rw [osemA_cond]
    split
    · exact ih₁ hw.1 s hs
    · exact ih₂ hw.2 s hs
  | seq c₁ c₂ ih₁ ih₂ =>
    intro hw s hs
    rw [osemA_seq]
    exact range_bind _ _ (osemA_measurable _) hS' (ih₁ hw.1 s hs)
      (fun s' hs' => ih₂ hw.2 s' hs')
  | «while» e c ih =>
    intro hw s hs
    rw [osemA_while]
    have hstep : ∀ n (s : St M), M.get s.1 t x ∈ S →
        range (fun s' : St M => M.get s'.1 t x ∈ S) (oubn (osemA c) (esem e) n s) := by
      intro n
      induction n with
      | zero => intro s _; simpa [oubn] using range_null _
      | succ n ihn =>
        intro s hs
        simp only [oubn]
        split
        · exact range_bind _ _ (oubn_measurable (osemA_measurable _) e.measurable n) hS'
            (ih hw s hs) (fun s' hs' => ihn s' hs')
        · exact range_dirac _ s hS' hs
    exact range_iSup _ hS' _ (oubn_monotone (osemA_measurable _) e.measurable s)
      (fun n => hstep n s hs)
  | @loc u y c ih =>
    intro hw s hs
    have hres : ∀ a' : M.heap, M.get a' t x ∈ S →
        M.get (M.set a' u y.name default) t x ∈ S := by
      intro a' ha'
      rw [M.get_set_ne _ _ a' y.name x _ (Or.inr hw.1)]; exact ha'
    rw [show osemA (.loc y c) s = (osemA c (M.set s.1 u y.name default, s.2)).map
        (fun s' => (M.set s'.1 u y.name default, s'.2)) from rfl,
      ← Measure.bind_dirac_eq_map _ (measurable_resetS y)]
    exact range_bind _ _ (Measure.measurable_dirac.comp (measurable_resetS y)) hS'
      (ih hw.2 _ (hres s.1 hs)) (fun s' hs' => range_dirac _ _ hS' (hres s'.1 hs'))

lemma measurableSet_get_eq (x : Vars ident .nat) (c : ℕ) :
    MeasurableSet {a : M.heap | M.get a .nat x.name ∈ ({c} : Set ℕ)} :=
  M.get_measurable _ _ (measurableSet_singleton c)

/-- A first statement that does not write `x` keeps its value, so the range of the sequence is
    that of the second statement from the states with the same value of `x`. -/
lemma range_seq_keep (x : Vars ident .nat)
    {c₁ c₂ : Cmd ident M} (hw : NoWrite x.name c₁)
    (P : M.heap → Prop) (hP : MeasurableSet {a | P a}) (s : St M)
    (h : ∀ s' : St M, M.get s'.1 .nat x.name = M.get s.1 .nat x.name →
      range (fun s'' : St M => P s''.1) (osemA c₂ s')) :
    range (fun s' : St M => P s'.1) (osemA (Cmd.seq c₁ c₂) s) := by
  rw [osemA_seq]
  exact range_bind _ _ (osemA_measurable _) (measurable_fst hP)
    (range_frame (t := .nat) x.name {M.get s.1 .nat x.name} (measurableSet_get_eq x _) c₁ 
      hw s rfl)
    (fun s' hs' => h s' (Set.mem_singleton_iff.mp hs'))

/-! ## Counted loop bodies -/

/-- `IncLast x c`: `c` is a sequence whose last statement is the increment `x := x + 1`
    and whose other statements do not write `x`.  It is syntactic. -/
def IncLast (x : Vars ident .nat) : Cmd ident M → Prop
  | .seq c₁ c₂ => NoWrite x.name c₁ ∧ (c₂ = Cmd.assign x (incW x) ∨ IncLast x c₂)
  | _ => False

/-- A body with `IncLast x` advances `x` by one, almost surely. -/
lemma range_incLast (x : Vars ident .nat) :
    ∀ c : Cmd ident M, IncLast x c → ∀ (s : St M) (v : ℕ), M.get s.1 .nat x.name = v →
      range (fun s' : St M => M.get s'.1 .nat x.name = v + 1) (osemA c s) := by
  intro c
  induction c
  case seq c₁ c₂ _ ih₂ =>
    rintro ⟨hw, h⟩ s v hs
    have hP : MeasurableSet {a : M.heap | M.get a .nat x.name = v + 1} :=
      measurableSet_eq_fun (M.get_measurable .nat x.name) measurable_const
    refine range_seq_keep x hw (fun a => M.get a .nat x.name = v + 1) hP s fun s' hs' => ?_
    rcases h with rfl | h
    · rw [osemA_assign]
      refine range_dirac _ _ (measurable_fst hP) ?_
      show M.get (M.set s'.1 .nat x.name (M.get s'.1 .nat x.name + 1)) .nat x.name = v + 1
      rw [M.get_set_eq, hs', hs]
    · exact ih₂ h s' v (hs'.trans hs)
  all_goals intro h; simp only [IncLast] at h

end Continuous
