import YM.FVAAlt2.Retro.Render
/-! # Instantiate Colors Fk entries from full Sheet without any future period readouts

Main result: REAL or complex representatives, meas/cts/gauge global; ray-Taylor exact through
r+a directions INCLUDING through moving backgrounds and alternate interpolation analytic paths.
This does not supply the later phase input estimates (no placement cost, can be global), it
compiles the **unmasked Wilson coefficients** period-by-period.

Cut-turn applies *outside germ* only: realize every jet via no-mask globally, compatible
with pricing food when using even $T.Level$ horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Block.Render
open RG Wilson Tree Exterior Lattice Precision MeasureTheory
open Comparison.RG02 Symmetry Symmetry.Orbit Comparison.RG02.Moving Moving.Path Moving.Shift Valence Assembly Adjacent
open Filter Function Set Finset Push.SectorMeasure Gauge CubicMatch Integral ConnectedActivityE6
open PertExtension.Series PertExtension.Series.Tested
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side} {r i k j a:ℕ} {δ γ:ℝ}
attribute [local instance] Gauge.frobInner
local notation "X"=> fieldDir G n 1
local notation "A"=> Config G n
local notation "E"=> (ℝ×X)
variable (C:Chi)(hF:Reliable G δ γ)
local notation "Ξ"=>outfit C δ (G:=G) (n:=n)
variable (P: Adjacent.Display (fieldDir G n 1))(D:Sheet r P) (b:ℕ)
variable (hv: ∀ i≤r,Valence.Level (↑(i+b):ℤ) (P i))
def sticker (δ:ℝ)(i:ℕ)(j:ℕ)(t:ℝ)(U:A) :ℂ:= t ^ ((i+b)-j) • Assembly.jet (P i) j (outfit C δ U)
def gift (δ:ℝ)(r:ℕ)(t:ℝ)(U:A):= ∑ i∈ range (r+1),∑ j∈range ((i+b)+1),sticker C P b δ i j t U
local notation "g"=>gift C P b δ r
include hF
lemma stature (h:ContDiff ℝ ω (P i))(he:j≤ i+b): GradeAt (i+b) (Bulk.projected (sticker C P b δ i j)):=by
    let y:= Assembly.jet (P i) j; let t:= Ξ ∘ represent; have ht:=cut_pan (n:=n) C hF; have h':GradeAt j y:= by
       refine ⟨ (Adjacent.levelJet h.contDiffAt _).smooth.contDiffAt,fun k hk=>?_⟩; rw [show iteratedFDeriv ℝ k y 0 =_ from Ranking.crop h.contDiffAt j k, if_neg (Nat.ne_of_lt hk)]
    have he':GradeAt ((i+b)-j+j) (Bulk.projected (sticker C P b δ i j)) := GradeAt.scale (f:=fun x:E=>x.1^((i+b)-j)) (GradeAt.shifts Prod.fst contDiffAt_fst rfl _) (GradeAt.coarse («g»:=Prod.snd) (GradeAt.coarse (f:=y) («g»:=t) h' ht (show t 0=0 by rw [show t 0=(Ξ) ( represent _ ) from rfl,Precision.link_one,cut_zero C hF])) contDiffAt_snd rfl)
    rwa [Nat.sub_add_cancel he] at he'
include D
lemma introduced : GradeAt b (Bulk.projected g) := GradeAt.list_sum (range (r+1)) (fun i x=>∑ j∈ range ((i+b)+1), (Bulk.projected (sticker C P b δ i j) x)) (fun i hi=> GradeAt.list_sum _ _ fun j hj=> ( stature C hF P b ( D.known _ (mem_range_succ_iff.mp hi) ) (mem_range_succ_iff.mp hj) ).lower (by omega)) -- omitted D? variable D lean not in statement. Need include D
lemma gauged (t:ℝ) : GaugeInvariant (g t) := by
    intro s U; apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj
    unfold sticker; rw [music C hF]; apply congr_arg
    let Q:= recolor (s 0) 1 (n:=n); rw [← Assembly.jet_continuous_right Q ( (D.known _ (mem_range_succ_iff.mp hi)).contDiffAt.of_le le_top )]; rw [show P i ∘ Q = P i from funext fun x=> D.color x (mem_range_succ_iff.mp hi) (s 0)]
lemma funded (t : ℝ) : Continuous (g t) := by
    unfold gift; exact continuous_finsetSum _ fun i hi=> continuous_finsetSum _ fun j hj=> (show Continuous (fun _:A=> t^ (i+b-j)) from continuous_const).smul ((Adjacent.levelJet (D.known i (mem_range_succ_iff.mp hi)|>.contDiffAt) j|>.smooth.continuous).comp (lawful C hF))
include hv
variable (F:ℝ→ fieldDir G n 1)(h:glows F)
lemma view : (fun t:ℝ=>g t (sample t (F t)))=fun t:ℝ=> (t:ℂ)^b*cover P r t (read C F t (δ:=δ)) :=by
    let y:=read C F (δ:=δ); funext t
    unfold gift cover; rw [ Finset.mul_sum ]; refine sum_congr rfl fun i hi=> ?_; rw [(hv i (mem_range_succ_iff.mp hi)).posted (y t), Finset.mul_sum, Finset.mul_sum ]
    refine sum_congr rfl fun j hj=> ?_; unfold sticker ;rw [← tends_ne C hF F t,Assembly.Clipper.weight, smul_smul,← pow_add,Nat.sub_add_cancel (mem_range_succ_iff.mp hj),Complex.real_smul ]; push_cast; rw [pow_add];ring
include D h
lemma evaluate : Adjacent.Shadow (r+b) (fun t=>g t (sample t (F t))) (fun t => (t:ℂ)^b*cover P r t (F t)):= by
    rw [view C hF P D b hv F]; have hU:= D.known; let V(t:ℝ):ℂ:= (t:ℂ)^b; let I (F:ℝ→X):= fun t=> cover P r t (F t); let y:= read C (δ:=δ) F; have ht: ContDiffAt ℝ ω V 0:=Complex.ofRealCLM.contDiff.contDiffAt.pow _; have hY: glows y:= readingPane C hF F h; have hg: ContDiffAt ℝ ω (I y) 0:= Call.escort _ hY r hU; have hh:= Call.escort (p:=P) F h r hU
    refine ⟨ht.mul hg,ht.mul hh,fun i hi=>?_⟩
    rw [ show motion _ i= _ from mono_price (f:=I y) hg, show motion _ i= _ from mono_price (f:=I F) hh ]; by_cases hx:b≤ i; swap; · rw [if_neg hx,if_neg hx]
    rw [if_pos hx,if_pos hx, show motion (I y) _= _ from Call.assessed y hY r hU (i-b) (by omega), show motion (I F) _= _ from Call.assessed F h r hU (i-b) (by omega) ]; exact D.follows y F (followsR C hF F h) hY h _ (by omega)
omit h
include D -- duplicate? 
-- enough at actual A and t
lemma earned (x:X)(i:ℕ)(hi:i≤r): Assembly.jet (Bulk.projected g) (b+i) (1,x)= P i x:=by
    let L:= (ContinuousLinearMap.id ℝ ℝ).smulRight ((1,x):E); let K:= fun t:ℝ=>cover P r t x
    have he:= Render.evaluate C hF P D b hv (fun _=>x) contDiffAt_const
    have hx : (fun t:ℝ=> g t (sample t x))=(Bulk.projected g) ∘ L:= funext fun t=> by change _= g (t*1) (represent (t • x)); rw [mul_one];rfl
    rw [ ← show L 1 =(1,x) from one_smul ℝ _, ← Assembly.jet_continuous_right L ((introduced C hF P D b).smooth.of_le le_top) ];
    change motion ( Bulk.projected g ∘ L ) (b+i) = _; rw [ ← hx ];
    rw [ show motion _ (b+i)= _ from he.aligns (b+i) (by omega), mono_price (f:=K) ( Call.escort (p:=P) (fun _=>x) contDiffAt_const r D.known ), if_pos (by omega), show b+i-b=i from by omega]
    -- reinterpret K as peval
    have hK: K=PertExtension.Series.Tested.peval (fun i=> P i x) r:=by
       funext t; unfold K cover PertExtension.Series.Tested.peval Zone.eval; apply sum_congr rfl fun j hj=> ?_; simp [Complex.real_smul]
    rw [hK,Adjacent.polary,if_pos hi] -- namespace
end YM.FVAAlt2.Block.Render
