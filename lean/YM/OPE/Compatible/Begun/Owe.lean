import YM.OPE.Compatible.Grid.Spoon
/-!
# Potential ordinary covariance algebra for anchor tests (strictly excludes torus bulk arrays)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier
variable {n c f:Side}{I J G:Type}
section flag
variable [Fintype I][Fintype J]
abbrev Health {I:Type} [Fintype I](A:Matrix I I ℝ)(v:I→ℝ):Prop:=∀ (w:I→ℝ),A*ᵥw=0→ v ⬝ᵥ w=0
lemma decides {x:I→ℝ} (h:∀ y:I→ℝ,y ⬝ᵥ x=0):x=0:=funext fun i=>by simpa using h (Pi.single i 1)
lemma entrusted (A:Matrix I J ℝ)(x:I→ℝ)(v:J→ℝ) : x ⬝ᵥ (A*ᵥ v)=Aᵀ*ᵥ x ⬝ᵥ v:=by rw [dotProduct_mulVec, Matrix.mulVec_transpose]
lemma invertG {A:Matrix I I ℝ} (x y:I→ℝ)(h:Aᵀ=A): x ⬝ᵥ (A*ᵥy)=y ⬝ᵥ (A*ᵥx):=by rw [entrusted,h,dotProduct_comm]
end flag
open Terp
variable {v u j r l: ℕ}{K:KernelChoices}
local notation "POT" n:arg => form 1 n
lemma KY (v:Train r)(h:4≤r): (Precision.K ((pink K.penalty v).acts n))ᵀ=Precision.K ((pink K.penalty v).acts n):=by
     have he : major (ShellRow K v) n=Precision.K ((pink K.penalty v).acts n)+grad n * (grad n)ᵀ:=by unfold major; rw [show (ShellRow K v).acts n=_ from Op_stays h v n]
     have ht:= (pondT (C:=K) h v n).eq; rw [conjTranspose_eq_transpose_of_trivial, he, transpose_add,transpose_mul,transpose_transpose] at ht; exact add_right_cancel ht
lemma KF (v:Train r)(h:4≤r): (Precision.K ((pink K.penalty v).acts n)).PosSemidef:= by
      let A:=Precision.K ((pink K.penalty v).acts n); have he:A.IsHermitian:=by unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact KY v h -- unfold
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg he; intro x; let H:= pink K.penalty v; obtain ⟨a,b,ha,hb,hQ⟩ := (heart_heats K.penalty K.penalty_pos h (fun i: Train r => i)).1.funds; let D:= d 1 n
      rw [star_trivial]; have he := (obey_band _ ((heart_heats K.penalty K.penalty_pos h (fun i: Train r=>i)).1.stock.whole v) (hQ v) n).2 (D*ᵥx); change 0≤ x ⬝ᵥ ((Dᵀ * H.acts n * D)*ᵥ x); rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,dotProduct_mulVec, vecMul_transpose]; apply le_trans (mul_nonneg ha.le _) he.1; simpa only [star_trivial] using dotProduct_star_self_nonneg (D*ᵥx)
lemma curtain0 (v:Train r)(h:4≤r)(x:POT n): Precision.K ((pink K.penalty v).acts n) *ᵥ x=0↔ (d 1 n)*ᵥx=0:=by
     let H:= (pink K.penalty v).acts n; let D:= d 1 n; let A:= Dᵀ*H*D; change A*ᵥx= _ ↔ _; constructor
     · intro ht; obtain ⟨a,b,ha,hb,hQ⟩ := (heart_heats K.penalty K.penalty_pos h (fun i: Train r => i)).1.funds; have he := (obey_band _ ((heart_heats K.penalty K.penalty_pos h (fun i: Train r=>i)).1.stock.whole v) (hQ v) n).2 (D*ᵥx)
       have hu: a*((D*ᵥx) ⬝ᵥ( D*ᵥ x)) ≤0:=by apply he.1.trans_eq; rw [←(show x ⬝ᵥ( A*ᵥx)=_ from (show x ⬝ᵥ( A*ᵥx)= (D*ᵥx) ⬝ᵥ( H*ᵥ( D*ᵥx)) from by unfold A; rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,entrusted,transpose_transpose])),ht,dotProduct_zero]
       let y:= D*ᵥx; have hy : y ⬝ᵥ star y=0:=le_antisymm (by rw [star_trivial]; exact nonpos_of_mul_nonpos_right hu ha) (dotProduct_star_self_nonneg y); exact dotProduct_star_self_eq_zero.mp hy
     intro ht; unfold A; rw [← Matrix.mulVec_mulVec,ht,mulVec_zero]
-- missing kernel
lemma misSym (n:Side): (missing n)ᵀ=missing n:=by ext ⟨u,i⟩ ⟨v,j⟩; simp [Resolvent.projected,eq_comm (a:=i)]
lemma rakeM (x:POT n) (u v:Site n) (z:TypeFace 1): (missing n*ᵥx) (u,z)=(missing n*ᵥ x) (v,z) :=by unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl ?_; rintro ⟨p,i⟩ _; change Resolvent.missing n (u,z) (p,i)*_=Resolvent.missing n (v,z) (p,i)*_; rw [Resolvent.projected,Resolvent.projected]
lemma rampM (x:POT n): d 1 n *ᵥ (missing n*ᵥ x)=0:=by funext p; obtain ⟨u,i⟩:=p; obtain ⟨a,h⟩:=plaqEquiv.surjective i; rw [plaq_map] at h; subst i; rw [d_plaquettes,rakeM _ _ u (coord a.val.2),rakeM _ (u+step a.val.2) u (coord a.val.1)]; simp
-- valid algebra
lemma lineSolve (v:Train r)(h:4 ≤ r)(q:POT n)(hp:Health (Precision.K ((pink K.penalty v).acts n)) q):
     let X:= lineC (ShellRow K v) n; let B:=Precision.K ((pink K.penalty v).acts n); B*ᵥ (X*ᵥ q)=q:=by
         intro X M; let y:= X*ᵥ q; let E:=d 0 n; let I:=missing n; change M*ᵥy=q
         have ht : I*ᵥq=0:=decides (fun t=>by rw [invertG t _ (misSym n)]; exact hp _ ((curtain0 v h _).2 (rampM t)))
         have hh:= congr_arg (fun T:Matrix (Body 1 n) _ ℝ=> T*ᵥ q) (neutralize (C:=K) n h v).1; simp only [← mulVec_mulVec,sub_mulVec,one_mulVec] at hh
         have hg:Eᵀ*M=0:=by unfold E M; rw [← KY v h (K:=K), ← transpose_mul,K_kills,transpose_zero] -- rfl
         have hz:Eᵀ*ᵥq=0:=decides (fun x=> by rw [entrusted,transpose_transpose,dotProduct_comm]; exact hp _ (by rw [mulVec_mulVec,K_kills,zero_mulVec]))
         unfold major at hh; rw [show (ShellRow K v).acts n=_ from Op_stays h v n, show missing n*ᵥ q=0 from ht,sub_zero,add_mulVec] at hh; let t:= Eᵀ*ᵥy
         have hf : M*ᵥy+E*ᵥt=q:=by unfold t; rw [mulVec_mulVec y E]; exact hh
         have h₁ : Eᵀ*ᵥ( E *ᵥ t)=0:=by rw [← hf,mulVec_add,mulVec_mulVec y Eᵀ,hg,zero_mulVec,zero_add] at hz; exact hz
         have h₂ : E*ᵥ t=0:=dotProduct_star_self_eq_zero.mp (by rw [star_trivial, entrusted,h₁,zero_dotProduct])
         rw [h₂,add_zero] at hf; exact hf
end YM.OPE.Cascade.Paver
