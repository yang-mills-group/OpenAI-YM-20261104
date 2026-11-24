import YM.OPE.Compatible.Mould.Can
/-!
# Top Vanishing characters. Paid shape earnings. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full Variance
variable {p₁:Clip}{u vν ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}
local notation "F!"=> Tracts G d τ
lemma LimitQ.plus {i:ℕ}{x y:Bead G d e}(h:LimitQ x i)(hz:LimitQ y i):LimitQ (x+y) i:=fun j hj=>by rw [Pi.add_apply,h j hj,hz j hj,add_zero]
lemma LimitQ.S {i:ℕ}{x:Bead G d e} (h:LimitQ x i)(c:ℝ):LimitQ (c • x) i:=fun j hj=>by rw [Pi.smul_apply,h j hj,smul_zero]
lemma LimitQ.Drop {i:ℕ}{x y:Bead G d e}(h:LimitQ x i)(hp:LimitQ y i):LimitQ (x-y) i:=fun j hj=>by rw [Pi.sub_apply,h j hj,hp j hj, sub_self]
lemma LimitQ.First {x y:Bead G d e}(h:LimitQ x (i+1))(hp:LimitQ y (i+1))(hh:∀ j:Fin (e+1),j.val=i→x j=y j): LimitQ (x-y) i :=by
     intro j hj; by_cases he:j.val=i; · rw [Pi.sub_apply,hh _ he,sub_self];
     exact LimitQ.Drop h hp j (by omega)
variable {r:Fin (e+1)}
lemma SprigT.plus {x y:F!}{a b:Bead G l e}(h:SprigT D₀ x r a)(hq:SprigT D₀ y r b): SprigT D₀ (x+y) r (a+b):=by
     exact ⟨by rw[map_add, Pi.add_apply,h.top,hq.top];rfl,h.cap.plus hq.cap,fun i hi=>by rw [map_add];exact LimitQ.plus (h.veil i hi) (hq.veil i hi)⟩
lemma SprigT.sizeZ {x:F!}{a:Bead G l e}(h:SprigT D₀ x r a)(c:ℝ): SprigT D₀ (c •x) r (c • a):=by
     exact ⟨by rw[map_smul,Pi.smul_apply,h.top];rfl,h.cap.Vert c,fun i hi=>by rw[map_smul];exact LimitQ.S (h.veil i hi) c⟩
lemma SprigT.nil : SprigT D₀ (0:F!) r 0:=by exact ⟨(by rw [map_zero]), Crop.from rfl, fun i hi=> by rw [map_zero]; exact fun _ _=>rfl⟩
lemma SprigT.subCrop {x y:F!}{a:Bead G l e}(h:SprigT D₀ x r a)(hp:Crop r.val y)(he:e<l+1): SprigT D₀ (x-y) r a:=by refine ⟨by rw [map_sub,Pi.sub_apply,h.top,fringP D₀ y he hp r le_rfl,sub_zero],h.cap.diff (hp.mono (Nat.le_succ _)), fun i hi=>?_⟩; rw [map_sub]; exact LimitQ.Drop (h.veil i hi) (fringP D₀ _ (by omega) hp)
lemma SprigT.Sum {x:I→F!}{u:I→ Bead G l e}(p:Finset I)(hp:∀ i∈p,SprigT D₀ (x i) r (u i)): SprigT D₀ (∑ i∈p,x i) r (∑ i∈p,u i):=by
     induction p using Finset.induction_on with| empty => rw [Finset.sum_empty,Finset.sum_empty]; exact SprigT.nil | insert i s hi ih=> rw[sum_insert hi,sum_insert hi]; exact (hp i (mem_insert_self ..)).plus (ih fun j hj=> hp _ (mem_insert_of_mem hj))
private lemma finite_coordinates {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) [FiniteDimensional ℝ W] (x : M → E) {u ν : M → ℝ}
    (hm : ∀ i, x i ∈ W) (hx : Wealth x u ν) :
    ∃ (n : ℕ) (b : Fin n → W) (c : Fin n → M → ℝ),
      (∀ j, Wealth (c j) u ν) ∧ ∀ i, x i = ∑ j, c j i • (b j).val := by
  let B := finBasis ℝ W
  let f (i : M) : W := ⟨x i, hm i⟩
  refine ⟨_, B, fun j i => B.coord j (f i), fun j => ?_, fun i => ?_⟩
  · exact aimW (B.coord j).toContinuousLinearMap (show Wealth f u ν from hx)
  · let z (j : Fin (Module.finrank ℝ W)) : W := B.coord j (f i) • B j
    have hsum : ∑ j, z j = f i := B.sum_repr (f i)
    change W.subtype (f i) = _
    rw [← hsum, map_sum]
    rfl

private lemma weighted_lifts {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {c : Fin n → M → ℝ} {p : Fin n → M → E} {u ν : M → ℝ}
    (hc : ∀ j, Wealth (c j) u ν) (hp : ∀ j, Wealth (p j) u 1) (hu : 1 ≤ u) (hv : 0 ≤ ν) :
    Wealth (fun i => ∑ j, c j i • p j i) u ν := by
  apply wealthset Finset.univ _ (fun j _ => ?_) hu hv
  exact mul_one ν ▸ wealth_mul (g := fun i => c j i • p j i) (hc j) (hp j)
    (fun i => le_of_eq (norm_smul ..))

private lemma sprig_basis_sum {N : ℕ} (W : Submodule ℝ (Tracts G d τ))
    (c : Fin N → ℝ) (p : Fin N → Tracts G d τ) (b : Fin N → Bead G l e)
    (h : ∀ j, p j ∈ W ∧ SprigT D₀ (p j) r (b j)) :
    (∑ j, c j • p j) ∈ W ∧ SprigT D₀ (∑ j, c j • p j) r (∑ j, c j • b j) :=
  ⟨W.sum_mem (fun j _ => W.smul_mem _ (h j).1),
    SprigT.Sum Finset.univ (fun j _ => (h j).2.sizeZ (c j))⟩

variable (T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
include T'
set_option maxHeartbeats 200000 in
lemma Paradigm (r: Fin (e+1))(he:e <l+1)(hx:∀ t,(V t).clip=p₁)(hp':r.val*l≤τ 0)(x:M→Bead G l e)(hz:0≤ vν)(hy: Wealth x u vν) (hm:∀ i,x i∈ Ghost G l e):∃ p:M→Tracts G d τ, Wealth p u vν∧∀ i,p i∈ Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀) i ∧ SprigT D₀ (p i) r (x i):=by
  obtain ⟨n, z, c, hc, hz'⟩ := finite_coordinates (Ghost G l e) x hm hy
  choose p hW hs using fun j : Fin n => Cune (hq := hq) Hp T' r he hx hp' (z j).val (z j).property
  refine ⟨fun i => ∑ j, c j i • p j i, weighted_lifts hc hW hq hz, fun i => ?_⟩
  rw [hz' i]
  exact sprig_basis_sum (S! i) (fun j => c j i) (fun j => p j i) (fun j => (z j).val) (fun j => hs j i)
end YM.OPE.Stroke
