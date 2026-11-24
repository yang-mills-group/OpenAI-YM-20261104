import YM.OPE.Compatible.Lob.Grids
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
variable (h:Aware d τ)
open Finset
lemma pylons (q p:Phase)(hp:q≤p)(x:bed G (d+q.val) (τ q)): armP G h q p hp x.val∈ bed G (d+p.val) (τ p):=by
     intro i; have hb:= sproutV (τ p) (d+p.val) (armP G h q p hp x.val); have ht:= hb.2 i; rw [armL] at ht ⊢; obtain ⟨h,hx,he⟩:= merit x.property i; exact ⟨⟨_,ht⟩,h,he,hx⟩
noncomputable def Len (G:Gauge)(h:Aware d τ)(x y:Phase)(hp:x≤y): bed G (d+x.val) (τ x) →L[ℝ] bed G (d+y.val) (τ y):= (armP _ h x y hp ∘L (bed G _ _).subtypeL).codRestrict _ (pylons h x y hp)
lemma TurnL (x y: Phase)(hp:x≤y)(v:bed G (d+x.val) (τ x)):
    lilies (τ y) _ _ ((Len G h x y hp v).val)= lilies (τ x) _ _ v.val:= armL h x y hp v.val
lemma SumGlide {f:Fin i→ Muse G}(v:Phase): Drift.glide (∑ i,f i) v=∑ i,Drift.glide (f i) v:=by
     funext j; rw [Finset.sum_apply]; by_cases ht:j<v; · simp_rw [glide_nil _ ht,Finset.sum_const_zero]
     unfold Drift.glide; simp_rw [if_neg ht]; exact Finset.sum_apply ..
lemma glider2 (p: Muse G)(x y:Phase)(hp:x.val+1=y.val): Drift.glide (Drift.glide p x) 1=Drift.glide p y:=by
    funext v; fin_cases x<;>fin_cases y<;> first | contradiction | (fin_cases v<;>rfl)
lemma glider_n (r:ℕ)(x:Phase): Drift.glide (Grid.lance (0:Script (Shade G) r)) x=0:=by
     convert! growS (r:=r) (G:=G) x (0:Script (Shade G) r) 0 using 1 -- `implicit r`
     all_goals simp
lemma pana (x y:Phase)(hp:x.val+1=y.val)(v:bed G (d+x.val) (τ x)):
   Drift.glide (baby (τ:=τ) x v.val) 1= baby (τ:=τ) y (Len G h x y (by change x.val≤ y.val;omega) v).val:=by
      unfold baby; rw [SumGlide]; simp_rw [glider2 _ _ _ hp,TurnL]; let X(i:ℕ):=Drift.glide (Grid.lance ((lilies (τ x) _ _ v.val) i)) y; let p:= d+x.val; let q:= d+y.val; change ∑ i:Fin (p+1),X i.val=∑ i:Fin (q+1), X i.val; have he: X (p+1)=0:=by unfold X; rw [(sproutV (τ x) _ v.val).1 _ (by unfold p;omega),glider_n]
      rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range] -- direction
      rw [show q=p+1 from by unfold q p;omega,sum_range_succ X (p+1),he,add_zero]
lemma ducal (x y:Phase)(hp:x.val+1=y.val)(v:bed G (d+x.val) (τ x)): trellisA G h (crestL G h x v)=crestL G h y (Len G h x y (by change x.val≤y.val;omega) v):=by
    apply Subtype.ext; apply bloomP G d τ; change Drift.spread G d τ (Candy _ h (ascendF _ h x v))= Drift.spread G d τ (ascendF _ h y _); rw [slideP,Drift.pick,Drift.pick]; exact pana h x y hp v
noncomputable def Gift (G:Gauge)(h:Aware d τ): Tracts G d τ→L[ℝ] Tracts G d τ:= ContinuousLinearMap.pi fun i=> if ht:i<1 then 0 else
     let j:Phase:=⟨i.val-1,by have h:= i.isLt;omega⟩; Len G h j i (by unfold j; change i.val-1 ≤ i.val;omega) ∘L ContinuousLinearMap.proj j
lemma tack (x:T!):Gift G h x (0:Phase)=0:=by unfold Gift; rw [ContinuousLinearMap.pi_apply,dif_pos (by decide)]; rfl
lemma tack1 (x:T!)(i j:Phase)(hv:i.val+1=j.val):Gift G h x j=Len G h i j (by change i.val≤j.val;omega) (x i):=by
    unfold Gift; rw [ContinuousLinearMap.pi_apply,dif_neg]; swap; · exact not_lt.mpr (show (1:Phase)≤j from (show 1≤j.val from by omega))
    have htX:j.val-1 < 3:= (by clear hv; have h:=j.isLt;omega); have he : i=⟨j.val-1,htX⟩:=Fin.ext (show i.val=_-1 from by omega); subst i;rfl
private lemma terminalCrest (x : T!) : trellisA G h (crestL G h 2 (x 2)) = 0 := by
  apply Subtype.ext
  funext i
  let p := (crestL G h 2 (x 2)).val
  change Candy G h p i = _
  fin_cases i
  · exact pal h p 0 (by decide)
  · erw [glee h p 1 0 rfl, show p 0 = 0 from (crestP G h 2 (x 2)).2 0 (by decide), map_zero]
    rfl
  · erw [glee h p 2 1 rfl, show p 1 = 0 from (crestP G h 2 (x 2)).2 1 (by decide), map_zero]
    rfl

private lemma nextCrest (x : T!) (i j : Phase) (hj : i.val + 1 = j.val) :
    trellisA G h (crestL G h i (x i)) = crestL G h j (Gift G h x j) :=
  (ducal h i j hj (x i)).trans (congrArg (crestL G h j) (tack1 h x i j hj).symm)

private lemma posePhaseSum (x : T!) :
    PoseQ G h x = ∑ i : Phase, crestL G h i (x i) := by
  change Drift.relief G h x = _
  unfold Drift.relief
  rw [_root_.sum_apply]
  rfl

private lemma threePhaseSum {V : Type*} [AddCommMonoid V] (a b : Phase → V)
    (ha : a 2 = 0) (hb : b 0 = 0) (h₀ : a 0 = b 1) (h₁ : a 1 = b 2) :
    ∑ i, a i = ∑ i, b i := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, ha, hb, h₀, h₁, add_zero, zero_add]

lemma social (x:T!): trellisA G h (PoseQ G h x)= PoseQ G h (Gift G h x):=by
  rw [posePhaseSum h x, posePhaseSum h (Gift G h x), map_sum]
  apply threePhaseSum
  · exact terminalCrest h x
  · rw [tack h x, map_zero]
  · exact nextCrest h x 0 1 rfl
  · exact nextCrest h x 1 2 rfl
end YM.OPE.Quit.Jac
