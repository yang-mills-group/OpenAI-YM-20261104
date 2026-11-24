import YM.MSbar.Pole.Feynman.Linked
/-!
# Continuum Wick prescription. All-order local counterterms.

Perform pole subtraction on graph + counterterms, including graphs with sources and tensor
slots. `menu` specifies all contractions for one named installation of vertices. Vertex
factor does NOT include the momentum conserving delta. Later use effective `Viewed`
and components of transported expressions. Overall Koszul graph factors can be applied
at the end. The IR setup here is `1-H_r`; arenas in the lattice scheme may differ. This
is genuine continuum dim-reg, *not* minimal log subtraction on a lattice. Poles and their
cancellation are theorems, including for graphs of composite operators. Need physical,
BRST, and IR results besides this (separately).
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Feynman
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Piece District
open scoped Topology ContDiff BigOperators Classical
variable {I V:Type} [Fintype I] [Nonempty I]

structure Menu (I V:Type) [Fintype I] [Nonempty I] where
  chart : Chart I V
  vertex : V→Cloud I
  localAt : ∀ v, let F := Leaf (I:=I) v;
                  Local chart.mom (F.weight chart) (vertex v) ∧ Shape (F.view chart) (F.opens chart) (vertex v)

namespace Menu
variable (C: Menu I V) (μ:ℝ)

/-- `body`: sum tagged by *actual* free integrations, accounts include environment
when scale changes. -/
structure Row (I:Type) where
  body : List (Piece I)
  ct : ℂ→ Cloud I

def solvent (F:District I V) (T:List (Piece I)) (H:ℂ→Cloud I) := Accounts T C.chart.mom (F.weight C.chart) (F.view C.chart) (F.opens C.chart) H
-- compute counterterm without any appeal to Wilson interaction!
def fault (F:District I V) (T:List (Piece I)) : ℂ→Cloud I :=
    if h:∃ H,C.solvent F T H then Classical.choose h else 0

def pick (C:Menu I V) (F:District I V) (e:I×I): Finset V:=
  if h: ∃ G,Gap G e F C.chart then Classical.choose h else ∅

def glimpse (F:District I V) (table: District I V→ Row I) (e:I×I): List (Piece I) :=
  let T:= F.thread C.chart e; let P:= F.less e
  if P.Crossing C.chart then
    (table P).body.map (leap T μ)
  else
    let L:=within (C.pick F e) e F C.chart; let R:=within (F.lands \ C.pick F e) e F C.chart
    assembly F e L C.chart (table L).body (table R).body

def total (F:District I V) (B:District I V→Row I) : List (Piece I) := F.paths.toList.flatMap (glimpse C μ F B)
def seed (F:District I V) : Row I:= if H:∃ i,F.lands={i} then ⟨[⟨0,fun _=> C.vertex (Classical.choose H)⟩],0⟩ else ⟨[],0⟩
def algorithm : ℕ→ District I V → Row I
| 0 => fun F=> C.seed F
| k+1 => fun F=> if F.paths=∅ then C.seed F else
             let T:= C.total μ F (algorithm k)
             let H:= C.fault F T
             ⟨remit T C.chart.mom (F.weight C.chart) H,H⟩

def run (F:District I V) := C.algorithm μ F.paths.card F
lemma atom {F : District I V} (p: F.Clear C.chart) (h:F.paths=∅) : Exact C.chart F (C.seed F).body := by
  obtain ⟨i,hi⟩:= one p h
  have hp : ∃ i,F.lands={i} := ⟨i,hi⟩; rw [seed,dif_pos hp]
  have hF : F=Leaf hp.choose:= by cases F; congr; exact hp.choose_spec
                                               -- specify
  have ht := native (C.vertex hp.choose) (C.localAt hp.choose).1 (C.localAt hp.choose).2
  exact (congr_arg (fun D=> Exact C.chart D [Piece.mk 0 (fun z=> C.vertex hp.choose)]) hF.symm) ▸ ht

variable {F:District I V}
private lemma decreases {e} (h:e∈F.paths) : (F.less e).paths.card < F.paths.card:=Finset.card_erase_lt_of_mem h
private lemma shrinks {e} (h:e∈F.paths) (S): (within S e F C.chart).paths.card < F.paths.card:= (Finset.card_filter_le _ _).trans_lt (decreases h)
private lemma press_equal (B D : District I V→Row I) (he: ∀ G, G.paths.card<F.paths.card→ B G=D G) : C.total μ F B=C.total μ F D:=by
  unfold total; apply List.flatMap_congr; intro e hp; have hh := Finset.mem_toList.mp hp; dsimp only [glimpse]; split_ifs
  · rw [he (F.less e) (decreases hh)]
  rw [he _ (shrinks C hh _),he _ (shrinks C hh _)]

lemma repeated {k l : ℕ} (h : F.paths.card ≤ k) (hk : k ≤ l) : C.algorithm μ k F=C.algorithm μ l F:=by -- k binder
  induction k generalizing F l with
  | zero =>
    have hp : F.paths=∅:= Finset.card_eq_zero.mp (by omega)
    cases l with
    | zero=> rfl
    | succ l => simp [algorithm,hp]
  | succ k ih =>
    obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (show l≠0 by omega); subst hl
    unfold algorithm; by_cases hb:F.paths=∅
    · rw [if_pos hb,if_pos hb]
    rw [if_neg hb,if_neg hb,C.press_equal μ (C.algorithm μ k) (C.algorithm μ l) (fun G hx=>ih (by omega) (by omega))]
lemma native_law (h : F.paths=∅) : run C μ F=C.seed F:=by unfold run; simp only [h,Finset.card_empty]; rfl
lemma means (h:F.paths.Nonempty):
    let B:= C.total μ F (C.run μ); let H:= C.fault F B
    C.run μ F=⟨Piece.remit B C.chart.mom (F.weight C.chart) H,H⟩:= by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr h).ne'; intro B H
  change C.algorithm μ F.paths.card F=_; rw [hk]; simp only [algorithm,if_neg h.ne_empty]
  have hp : C.total μ F (C.algorithm μ k)=B:=C.press_equal μ _ _ fun G hp=> (repeated C μ (F:=G) (le_refl G.paths.card) (by omega)).symm
  rw [hp]
private lemma mends (F:District I V) {f:List (I×I)} {B : I×I→ List (Piece I)} (h : ∀ x∈f,Young C.chart F (B x)) : Young C.chart F (f.flatMap B) := by
  induction f with
  | nil => exact Flag.zero
  | cons i x ih=> exact Flag.add (h i (by simp)) (ih (fun v hv=> h v (List.mem_cons_of_mem _ hv)))
lemma aspired (h:F.Clear C.chart) (hμ : 0<μ) (hh : ∀ G:District I V, G.Clear C.chart → G.paths.card < F.paths.card → Exact C.chart G (C.run μ G).body) : Young C.chart F (C.total μ F (C.run μ)) := by
  apply mends; intro x hx; have he:= Finset.mem_toList.mp hx; dsimp only [glimpse]; split_ifs with hb
  · exact herald h he (hh _ (District.Clear.pauses h he hb) (decreases he)) hμ
  have hp : Gap (C.pick F x) x F C.chart:=by rw [pick,dif_pos (h.splits he hb)]; exact Classical.choose_spec (h.splits he hb)
  have hk := h.content he hp
  exact District.across h he hp (hh _ hk.1 (shrinks C he _)) (hh _ hk.2 (shrinks C he _))
lemma pays (h:F.Clear C.chart) (hμ:0<μ) (k : ℕ) (hk:F.paths.card ≤ k) : Exact C.chart F (C.run μ F).body:= by
  induction k generalizing F with
  | zero => have hp:F.paths=∅:= Finset.card_eq_zero.mp (Nat.le_zero.mp hk); rw [native_law C μ hp]; exact atom C h hp
  | succ k ih=>
    by_cases hv : F.paths.Nonempty
    · have hs := aspired C μ h hμ fun G hg hi=> ih hg (by omega)
      let B:= C.total μ F (C.run μ); have hp : ∃ H, solvent C F B H:= matures hs h.notations
      rw [means C μ hv]; unfold fault; rw [dif_pos hp]; exact (Classical.choose_spec (show ∃ H, Accounts B _ _ _ _ H from hp)).serves hs h.notations
    have hp : F.paths=∅:= Finset.not_nonempty_iff_eq_empty.mp hv; rw [native_law C μ hp]; exact atom C h hp

lemma done (h:F.Clear C.chart) (hμ:0<μ) : Exact C.chart F (C.run μ F).body:=pays C μ h hμ _ le_rfl
lemma sales (h:F.Clear C.chart)(hμ:0<μ) (hp:F.paths.Nonempty) :
    C.solvent F (C.total μ F (C.run μ)) (C.run μ F).ct:= by
  have ht := aspired C μ h hμ fun _ h _=> done C μ h hμ
  have hx : ∃ H,solvent C F (C.total μ F (C.run μ)) H:= matures ht h.notations
  rw [means C μ hp]; unfold fault; rw [dif_pos hx]; exact Classical.choose_spec hx
end Menu
end YM.MSbar.Pole.Feynman
