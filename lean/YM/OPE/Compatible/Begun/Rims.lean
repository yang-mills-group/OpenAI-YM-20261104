import YM.OPE.Compatible.Words.Stem
/-!
# FormReader at ordinary trunks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j m:ℕ}
section
noncomputable def flats (G:Gauge)(n:Side): Bid.Dir G n≃L[ℝ] Vec G n 1:=(spool G n).trans ((deckW G n).symm.toContinuousLinearEquiv)
lemma flatX (x:Bid.Dir G n): flats G n x=flatten x:=by funext j; obtain ⟨a,h⟩:= (station G n).surjective j; rw [← h]; exact congr_fun ((deckW G n).apply_symm_apply (spool G n x)) a
variable (S: StepData c f)(he:Odd S.ratio.count.val)
local notation "F!"=> forest S.ratio he
lemma padQR (x: Bid.Dir G c)(y: AxisChart G F!): flatten (ribz S he (x,y))=insertion (plant F!)*ᵥ cash (countingBasis F! G) y:=by
     let T:= forest S.ratio he; rw [show cash (countingBasis T G) y=active T y from funext fun i=>rangers_fee ..,chart_flow]; congr 1; funext i; obtain ⟨p,a⟩:=i; obtain ⟨z,rfl⟩:=axisEquiv.surjective a
     change edgeColor (Stationary.pad T y) (p,z)= Exterior.collect G (Bid.stretch T (0,y)) (p,z); rw [Work.F01.collect_vertical]; split
     next h=> exact Stationary.pad_trunk T y ⟨_,h⟩
     next h=> exact Stationary.pad_free T y ⟨_,h⟩
variable (a: Cross S.ratio.count (TypeFace 1) (TypeFace 1))(g:Bid.Dir G c→AxisChart G (forest S.ratio he)){K:Sponsor G}{Q:Seasons K} {l b:ℝ}(D: Alps K Q i l)(U:Boxes G S.patch S.kernel)
variable (t:S.Choices)
variable (h: licensed S he U D.clip D.live (installed S.ratio a) D.sky g)
variable (X:Rill.FibreRep S he U t (i:=i) D g b)
def vertD : AxisChart G F!→L[ℝ] Vec G f 1:= (flats G f).toContinuousLinearMap ∘L (ribz S he ∘L ContinuousLinearMap.inr ℝ (Bid.Dir G c) _)
def Master := tensor G (extracted S F! (installed S.ratio a))
include h
lemma uprush (x:Bid.Dir G c)(y:AxisChart G F!):
     let V:= Fiber.drape (Libra.Keys G (Body 1 c)) (Libra.Keys G (forest S.ratio he).Free) X.L.M
     flats G f (ribz S he (V (x,y)))=Master S he a*ᵥ flats G c x+ vertD S he y:=by
       intro V; rw [show V (x,y)= fieldT (cabin g) x+ (0,y) from lytic S he U t h X x y, map_add,map_add]
       congr 1; rw [folds t h.2.1, flatX, padQR, flatX]; let I:=forest S.ratio he; let A:= Master (G:=G) S he a; rw [show cash (countingBasis I G) _=reduce G S I*ᵥ( A *ᵥ flatten x) from ?_]; exact projects I _ (spunE _ I a _); rw [reduce_actual]; funext u; exact plantT t h.2.1 h.2.2.1 x u
omit h
lemma fortune : chamber X.L.Q (vertD S he)= (FreeResolvent.insertion (plant F!))* (FUND S he U)⁻¹ * (FreeResolvent.insertion (plant F!))ᵀ :=by
      let A:=FUND S he U; let T:=forest S.ratio he; let Y:= FreeResolvent.insertion (plant T (G:=G)); let P:= countingBasis T G; let C:= X.L.Q; have hm : IsUnit A.det:=(ulk_force S he U).det_pos.ne'.isUnit
      let f(i:FreeResolvent.Slot G f 1):= coQ (vertD S he) i; have ht(i y): f i y=(Y*ᵥ cash P y) i:= by change flats G _ (ribz S he (0,y)) i=_; rw [flatX, padQR]
      ext i j
      let v:= Yᵀ*ᵥ Pi.single j 1; let w:= A⁻¹*ᵥ v; let x:AxisChart G T:= (cash P).symm w; have hg : C.P x=f j:=by
           apply LinearMap.ext; intro z; rw [C.turns, show C.P z x = _ from X.P0 z x]; change cash P z ⬝ᵥ (A*ᵥ cash P x)=_; rw [show cash P x=w from (cash P).apply_symm_apply _,ht]; unfold w; rw [Matrix.mulVec_mulVec _ A,Matrix.mul_nonsing_inv _ hm,Matrix.one_mulVec]; unfold v; rw [dotProduct_comm,← entrusted, single_one_dotProduct]
      change C.wick (f i) (f j)=(Y*A⁻¹* Yᵀ) i j; rw [wix_sym (μ:=Chart.tangent G T.Free) C]; change (f i (C.inverse (f j)))=(Y*A⁻¹* Yᵀ) i j; rw [← hg,Law.solves, ht, show cash P x=w from (cash P).apply_symm_apply _]; unfold w v; rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]; rw [Matrix.mulVec_single_one, Matrix.mul_assoc]; rfl
end
end YM.OPE.Cascade.Paver
