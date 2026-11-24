import YM.RGComparison.Core16.Parcel.Pose
import YM.RGComparison.Core16.Stem.Accuracy
import YM.RGComparison.Core16.Insertions
/-!
# Physical output data with calibrated Proto.F decorations

Positions at THE true period torus, all slots independent (repetition permitted); future consumer
OPE only separated labels. Here support of a payload on S.S actual steps even for torus wrap.
Asserts for Π at same prior law; point price planning post-stages. C supplied per Replica.A
billing. Keep all momentum orders and finite demand printed in endpoint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Spool
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Lumen Lumen.Planet Parcel Parcel.Oven Next.Fluctuations Finset Complex
open Lumen.Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius

-- permit ANY translation-cov cylindrical kernel with a priced zero at the test order. For this
-- transfer only near-field proof uses analytic Ψ through Pose, same Pop as basis calibration.
structure Lamp (G:Gauge) where
    stencil : Finset Cover
    action : CoverConfig G→ℂ
    order : ℕ
    regular : Continuous action
    symmetry : GaugeInvariant action
    books : LocalOn (stencil:Set Cover) action
    basis : ∃ (m:ℕ)(B:Fin m→ RG.Slot)(T:Bid.Pose G m), action= Bid.lumin T ∘ Bid.mapped B ∧ Bid.lows T order
variable {G:Gauge}{d:ℕ}

def investment {F:Labels.Frame G d}{H: Source.Hol G}{S:Source.SectionData F}(hS:S.Sound H)(H':Bid.pop S)(i:F.Index): Lamp G:=
   { stencil:=S.stencil
     action:= S.evaluate (Pi.single i 1)
     order:= (F.grades i).2
     regular:= S.continuous_evaluate _
     symmetry:= hS.gaugeInvariant _
     books:= S.cylinder_local _
     basis:=by obtain ⟨m,B,-,T,h,h0⟩:= H' i; exact ⟨m,B,T,h,h0⟩ }

variable {c f n: Side} (S : StepData c f)(T:Forest S.ratio)
variable {ι:Type}[Fintype ι](J:ι→ Lamp G)

-- coherent count & actual lift before world joining any marks.
def Light (p : Lamp G) (n : Side)(x : Site n) (U : Config G n):= p.action (expandAt x U)
def power := ∑ i, (J i).order

def tally (x:ι→Site f)(U: Config G f):ℂ:= ∏ i, Light (J i) f (x i) U
lemma tally_invariant (x:ι→Site f): GaugeInvariant (tally J x):=by
    intro k U; apply prod_congr rfl fun i _=> ?_; unfold Light; rw [expandAt_gauge, (J i).symmetry]
lemma tally_cont (x:ι→Site f): Continuous (tally J x):=by unfold tally Light; exact continuous_finsetProd _ fun i _=> (J i).regular.comp (by unfold expandAt; fun_prop)

abbrev Reel (p : Lamp G):= ↥p.stencil × Axis
abbrev Slice (J:ι→Lamp G):= Σ i, Reel (J i)

def wind (p : Lamp G)(u:Sky G (Reel p)): CoverConfig G:= fun i=> if h:i.1∈p.stencil then u (⟨i.1,h⟩,i.2) else 1

def exhibit (J:ι→Lamp G)(u:Sky G (Slice J)):ℂ:= ∏ i,(J i).action (wind (J i) (fun x=> u ⟨i,x⟩))

def legs (x:ι→Site f) (j:Slice J): Edge (Site f):= (wrap f j.snd.1.val+x j.fst,j.snd.2)

def earns (x:ι→Site f) : Stuff G T.Free (Slice J):= fun j=> if h: legs J x j∈T.trunks then .inr 0 else .inl ⟨legs J x j,h⟩

lemma exhibition (x:ι→Site f)(U:Config G f): exhibit J (U ∘ legs J x)= tally J x U:=by
    apply prod_congr rfl fun i _=> ?_; apply (J i).books; intro e hi hI; unfold wind; rw [dif_pos (show e.1 ∈ (J i).stencil from hi)]; rfl
lemma wind_cont (p:Lamp G): Continuous (wind p):=by apply continuous_pi; intro i; unfold wind; split; exact continuous_apply _; exact continuous_const
lemma exhibit_cont : Continuous (exhibit J):=by unfold exhibit; refine continuous_finsetProd _ fun i _=> (J i).regular.comp ((wind_cont _).comp ?_); exact continuous_pi fun j=> continuous_apply _

def sight (y:Slice J→G.Color) := exhibit J (fun i=> launch (y i))
def look (i:Bool): ℂ→L[ℝ] ℝ:= if i then Complex.imCLM else Complex.reCLM
lemma encouraging : ∃ C:ℝ,0≤C ∧ ∀ i x, ‖look i (exhibit J x)‖ ≤ C:= by
    choose c hc using fun i=> (isCompact_range ((look i).continuous.comp (exhibit_cont J)|>.norm)).bddAbove
    let v:= ∑ i:Bool,|c i|
    refine ⟨v,sum_nonneg (fun _ _=> abs_nonneg _),fun i x=>?_⟩; exact ((hc i (Set.mem_range.mpr ⟨x,rfl⟩)).trans (le_abs_self (c i))).trans (single_le_sum (fun i _=>abs_nonneg (c i)) (mem_univ i))

variable (B:ι→Site f)
def echo (i:Bool): Melody G T.Free:= fun _ z => look i (tally J B (T.drape z))

lemma offers {L D:Type}[Fintype D]{X: Shelf G L D} (H:Good X) (i:Bool) {C:ℝ}(he:∀x,‖look i (exhibit J x)‖ ≤ C) : Visible X (look i ∘ sight J) (echo S T J B i) (earns S T J B) (Fintype.card (Slice J)) C := by
    let F := earns S T J B; let I:= univ.biUnion (fun i=> Sum.elim (fun i=>({i}:Finset _)) (fun _=>∅) (F i))
    have hx (p:Slice J)(j:T.Free)(hp:F p=.inl j):j∈I:=mem_biUnion.mpr ⟨p,mem_univ _,by rw [hp]; exact mem_singleton_self _⟩
    refine ⟨fun g hg=> havenreal ((look i).continuous.comp ((tally_cont J B).comp T.continuous_drape)),fun g hg x=>?_,I,?_,?_,?_⟩
    · change ‖look i (tally _ _ _)‖ ≤ _; rw [← exhibition J _ (T.drape x)]; exact he _
    · refine (card_biUnion_le).trans ?_; refine (sum_le_sum (g:=fun _=>1) (fun i _=>?_)).trans_eq (by simp); cases F i <;> simp
    · intro j; unfold F earns at *; split; change ‖(0:G.Color)‖ ≤ _; simp [H.thick.1.le]; exact hx j _ (dif_neg (by assumption))
    intro g hg he x hv; change look i (tally _ _ _)=look i (exhibit _ _); rw [← exhibition J _ (T.drape x)]; apply congrArg (fun x=> look i (exhibit J x)); funext j
    let z:= legs J B j
    change T.drape x z=launch (g • book F g x j); unfold book; by_cases hh:z∈ T.trunks
    · rw [show F j= .inr 0 from dif_pos hh, T.on_tree x ⟨_,hh⟩]; change _=launch (g • (0:G.Color)); simp [Lumen.launch_zero]
    let q:T.Free:=⟨z,hh⟩; have hy:F j=.inl q:=dif_neg hh
    rw [hy,T.off_tree x q]; change x q=launch (g • (g⁻¹ • G.curvature (x q))); rw [smul_inv_smul₀ he.ne',H.reenter]; exact ((hv q (hx j q hy)).trans (half_lt_self H.extent.1))

end YM.RGComparison.Core16.Spool
