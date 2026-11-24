import YM.OPE.Compatible.Mould.Army
/-!
# Theta lift from registered series. subtract exact invisibility.W.K\CAP
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic Variance
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J}{w:ℝ}{D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full
variable {p₁:Clip}{u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(L:Lance X)
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
local notation "F!"=>Tracts G d τ
local notation "D!" x=>Topic.Dross Hp Z a x
variable (he:e<l+1) (hz:0≤ν)
lemma stepDiff {W:Type} [AddCommGroup W][Module ℝ W]{G:Type}[AddCommGroup G][Module ℝ G](f:W→ₗ[ℝ] G)(x y: W)(h:f x=f y): f (y-x)=0:=by rw [map_sub,h,sub_self]
private lemma reduced_coordinate (x : Fin (e+1)) (p : Bead G l e) (v : Tracts G d τ)
    (hs : SprigT D₀ v x p) (hv : LimitQ p (x.val+1)) (he : e < l+1) :
    LimitQ (p-tag D₀ e v) x.val := by
  apply LimitQ.First hv (fringP D₀ v he hs.cap)
  intro j hj
  obtain rfl : j = x := Fin.ext hj
  exact hs.top.symm

private lemma extend_head (he : e < l+1) (hu : 1 ≤ u) (hν : 0 ≤ ν)
    (Y : M → Submodule ℝ (Tracts G d τ)) (x : Fin (e+1)) (prev : Head_ x.val e ν U Y)
    (p : M → Bead G l e) (hw : Wealth p u ν)
    (hρ : ∀ j, p j ∈ Ghost G l e ∧ LimitQ (p j) (x.val+1)) (z : ∀ j, U.flag e j)
    (hz : Wealth (fun j => (z j).val) u ν) (hs : ∀ j, (z j).val ∈ Y j ∧ SprigT D₀ (z j).val x (p j))
    (hg : ∀ j, tag D₀ e (z j).val ∈ Ghost G l e) :
    ∃ v : ∀ j, U.flag e j, Wealth (fun j => (v j).val) u ν ∧
      ∀ j, (v j).val ∈ Y j ∧ Crop (x.val+1) (v j).val ∧ tag D₀ e (v j).val = p j := by
  let t (j : M) := tag D₀ e (z j).val
  have ht : Wealth t u ν := aimW (tag D₀ e) hz
  have hr j : (p-t) j ∈ Ghost G l e ∧ LimitQ ((p-t) j) x.val :=
    ⟨(Ghost G l e).sub_mem (hρ j).1 (hg j), reduced_coordinate x (p j) (z j).val (hs j).2 (hρ j).2 he⟩
  obtain ⟨f, hf, hF⟩ := prev (p-t) (subW hu hν hw ht) hr
  refine ⟨z+f, anthW hu hν hz hf, fun j => ⟨(Y j).add_mem (hs j).1 (hF j).1,
    (hs j).2.cap.plus ((hF j).2.1.mono (Nat.le_succ _)), ?_⟩⟩
  change tag D₀ e ((z j).val + (f j).val) = _
  rw [map_add, (hF j).2.2]
  change t j + (p j - t j) = _
  abel

include T' hz hq he
set_option maxHeartbeats 200000 in
lemma NeedleHeel (x: Fin (e+1))(y:M→Bead G l e)(hx:∀ j, (hj:j<e)→SonE j (hj.trans he) ν U (Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)) (Topic.Dross Hp Z a j))
   (i:ℕ)(hi:i≤ e)(p:∀ j,U.flag i j)(hw:Wealth (fun j=>(p j).val) u ν)(h:∀j, (p j).val∈ S! j∧ SprigT D₀ (p j).val x (y j)):
   ∃ v:∀ j,U.flag e j, Wealth (fun j=>(v j).val) u ν ∧∀ j, (v j).val∈S! j∧SprigT D₀ (v j).val x (y j):=by
     induction hi using Nat.decreasingInduction with
     | self=> exact ⟨p,hw,h⟩
     | of_succ i hI IH=>
        let idx:= hI.trans he; let f(j:M):= U.read i idx j (p j); have he'(j):LimitQ (UΦ Z idx (f j) 0) x.val:=by unfold f; rw [discU idx]; exact (h j).2.veil _ hI
        obtain ⟨v,hv,hV⟩:= hx i hI f (U.bulk idx p hw) (fun j=>stockMe Hp T' j (p j) (h j).1) 0 (Nat.zero_le _) (fun _=>trims.be _) x.val he'
        let a(j):= p j-v j; have hA(j):(a j).val∈ U.flag (i+1) j:= (U.depth i j idx (a j)).2 (stepDiff (G:=Mint Z i) (U.read i idx j) (v j) (p j) (show U.read i idx j (v j)=U.read i idx j (p j) from (hV j).2.1)); apply IH (fun j=>⟨(a j).val,hA j⟩) (subW hq hz hw hv) fun j=> ⟨Submodule.sub_mem (S! j) (h j).1 (hV j).1,SprigT.subCrop (h j).2 (hV j).2.2.2 he⟩
private lemma lift_basis_flag (x : Fin (e+1)) (p : M → Bead G l e)
    (hx : ∀ j, (hj : j < e) → SonE j (hj.trans he) ν U (S!) (Topic.Dross Hp Z a j))
    (hclip : ∀ i, (V i).clip = p₁) (hw : x.val*l ≤ τ 0)
    (hpw : Wealth p u ν) (hm : ∀ j, p j ∈ Ghost G l e) :
    ∃ v : ∀ j, U.flag e j, Wealth (fun j => (v j).val) u ν ∧
      ∀ j, (v j).val ∈ S! j ∧ SprigT D₀ (v j).val x (p j) := by
  obtain ⟨q, hq', hrow⟩ := Paradigm (Z := Z) (U := U) (V := V) (a := a) (hq := hq)
    Hp T' x he hclip hw p hz hpw hm
  let y (j : M) : U.flag 0 j := ⟨q j, by rw [U.first]; exact Submodule.mem_top⟩
  exact NeedleHeel (Z := Z) (U := U) (V := V) (a := a) (hq := hq) Hp T' he hz x p hx
    0 (Nat.zero_le e) y hq' hrow

include L
set_option maxHeartbeats 200000 in
lemma neal (hx:∀ j,(hj:j<e)→ SonE j (hj.trans he) ν U (Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)) (Topic.Dross Hp Z a j))
   (h':∀ i,(V i).clip=p₁)(hw:e*l≤τ 0): HostE e ν U (S!) :=by
      intro k; induction k with
      | zero=>
           intro p hh hA; refine ⟨0,wealthZ u ν,fun i=>⟨(S! i).zero_mem,Crop.from rfl,?_⟩⟩; erw[Pi.zero_apply,Submodule.coe_zero,map_zero]; exact funext fun j=> ((hA i).2 j (Nat.zero_le _)).symm
      | succ n IH=>
           intro p hp hρ; by_cases h:n≤e; swap;· obtain ⟨q,hq,ht⟩:= IH p hp (fun i=>⟨(hρ i).1,fun j hj=> by omega⟩); refine ⟨q,hq,fun i=>⟨(ht i).1,(ht i).2.1.mono (Nat.le_succ n),(ht i).2.2⟩⟩
           let x : Fin (e+1) := ⟨n, by omega⟩
           obtain ⟨z, hF, hX⟩ := lift_basis_flag (Z := Z) (U := U) (V := V) (a := a) (hq := hq)
             Hp T' he hz x p hx h' ((Nat.mul_le_mul_right l h).trans hw) hp (fun j => (hρ j).1)
           exact extend_head (Z := Z) (U := U) he hq hz (S!) x IH p hp hρ z hF hX
             (fun j => NemTag (Z := Z) (U := U) (V := V) (a := a) (hq := hq) Hp T' L he j (z j) (hX j).1)
end YM.OPE.Stroke
