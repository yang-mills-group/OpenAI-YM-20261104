import YM.Integration.WilsonOriginalPublicTrialPhaseActual
import YM.RG05Readout.Capture.Shelf

/-! Reindex the actual full menu by a single unit coordinate, preserving every ordinary subface. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhasePad
open Function Finset Filter MeasureTheory Lattice Wilson RG Labels Source MergeProof MergeProof.Accent Marker
open Extra.Trajectories RG05Readout RG05Readout.Many RG05Readout.Pantry RG05Readout.Address
open Further.ShellBirth49.Fusing
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]
def pad (i:V):Unit×V:=((),i)
def lift (s:(Stock.census (Unit×V)).Mode):(Stock.census V).Mode:=
  ⟨s.val.image Prod.snd,Finset.mem_powerset.mpr (Finset.subset_univ _)⟩
theorem license : License (Stock.census (Unit×V)) (Stock.census V) pad:=
 fun i _=>Finset.mem_powerset.mpr (Finset.subset_univ i)
theorem lit (i:(Stock.census V).Mode):Lit (Stock.census (Unit×V)) pad i.val:=
 ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),fun _ _ _ _ h=>congrArg Prod.snd h⟩
theorem mode (s:(Stock.census (Unit×V)).Mode)(p:Poly (Stock.census V)):
    (feed (fun _=>1) license p).part s=p.part (lift s):=by
  classical
  have undo (j:Unit×V):pad j.2=j:=by cases j with| mk u j=>cases u;rfl
  have fwd (i:(Stock.census V).Mode)(s:(Stock.census (Unit×V)).Mode):
      (lit i).climb=s ↔ i=lift s:=by
    constructor
    · intro h;apply Subtype.ext
      rw [←h]
      simp [lift,Lit.climb,Finset.image_image,pad,Function.comp_def]
    · rintro rfl
      apply Subtype.ext
      simp [lift,Lit.climb,Finset.image_image,Function.comp_def,undo]
  rw [parts_of_feed,Finset.sum_eq_single (lift s)]
  · rw [move,dif_pos (lit _),Poly.part_send,if_pos (((fwd _ _).mpr rfl).symm)]
    simp
  · intro j _ ne
    rw [move,dif_pos (lit _),Poly.part_send,if_neg (fun h=>ne ((fwd _ _).mp h.symm))]
  simp

theorem alcove {B:Rep G n}{X:V→Three G n}{F:Config G n→Poly (Stock.census V)}
    {o:V→Site n}{w:V→ℝ}{t e c α β b y E:ℝ}
    (h:Alcove B X F o w t e c)(law:B.Lawful α β b y E)(integ:Integrable F (prior G _))
    (pos:∀i,0<w i)(he:0≤e)(hc:0≤c):
    Alcove B (fun j:Unit×V=>X j.2) (fun U=>feed (fun _=>1) license (F U))
      (fun j:Unit×V=>o j.2) (fun j:Unit×V=>w j.2) t e c:=by
  classical
  have hb (j:Unit×V): univ.filter (fun i:V=>pad i=j)={j.2}:=by
    ext i
    rcases j with ⟨⟨⟩,j⟩
    simp [pad]
  have no (j:Unit×V):(univ.filter (fun i:V=>pad i=j)).card≤1:=by rw [hb];simp
  have h':=h.group (δ:=pad) (q:=fun j:Unit×V=>o j.2) (w':=fun j:Unit×V=>w j.2)
    (v:=fun _=>1) (N:=1) (h:=license) law integ rfl (by decide) he hc pos (fun j=>pos j.2) (by simp [pad]) no
  have eq:combine pad (fun _=>1) X=(fun j:Unit×V=>X j.2):=by
    funext j
    rw [solo_com]
    change ∑ i ∈ univ.filter (fun i:V=>pad i=j), (1:ℂ) • X i=X j.2
    rw [hb];simp
  simpa only [eq] using h'

end YM.Integration.WilsonOriginalPublicTrialPhasePad
