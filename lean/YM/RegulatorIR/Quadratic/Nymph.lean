import YM.RegulatorIR.Quadratic.Systems
import YM.PertExtension.GaussianIBP

/-!
# Schur on restricted orbit fibers
Real finite regulator. Pos demand proved in separate gauge stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram Matrix PertExtension GaussianScore Filter Set Metric
open scoped ENNReal NNReal BigOperators Classical Topology Matrix
variable {W X I J: Type} {c:ℝ}
variable [Fintype X] [DecidableEq X] [Fintype J][DecidableEq J]
variable {a:X→Prop}{K N:Matrix X X ℝ}{L : Matrix J J ℝ}{Q : Matrix J X ℝ} {D:Matrix X J ℝ}

def phase [Fintype I] (K:Matrix I I ℝ) (x:I→ℝ):= x ⬝ᵥ (K *ᵥ x)/2
def heatPay (c:ℝ)(Q:Matrix J X ℝ)(x:X→ℝ)(v:J→ℝ):= c*((v-Q *ᵥ x) ⬝ᵥ (v-Q *ᵥ x))/2
def StripQ (a:X→Prop)(x:X→ℝ):Prop:=∀ i,¬a i → x i=0
namespace GridQ
variable (G:GridQ c a K L Q D N)
include G
lemma passesV (v:J→ℝ) i (hi:a i): (diagStiff c K Q *ᵥ (D *ᵥ v)) i=( (c • (Q.transpose*ᵥ v)) : X→ℝ) i:=by
 rw [mulVec_mulVec, ← Matrix.smul_mulVec]; apply Finset.sum_congr rfl;intro j _; dsimp only; rw [G.passes i j hi];rfl
lemma clipped (v:J→ℝ): StripQ a (D *ᵥ v):=by intro i hi; apply Finset.sum_eq_zero;intro j _; dsimp only; rw [G.means i j hi,zero_mul]
lemma style : (diagStiff c K Q).transpose=diagStiff c K Q:=by rw [diagStiff,transpose_add,G.turn, transpose_smul,transpose_mul,transpose_transpose]

lemma eye {x : X→ℝ}(h : StripQ a x)(v:J→ℝ): x ⬝ᵥ (diagStiff c K Q *ᵥ (D *ᵥ v)) = c*(v ⬝ᵥ (Q*ᵥ x)):= by
 let R:=diagStiff c K Q
 calc
   _= x ⬝ᵥ ((c • (Q.transpose*ᵥ v)) : X→ℝ):= by apply Finset.sum_congr rfl;intro i _; by_cases hi:a i <;> first | (rw [G.passesV v i hi]) | (rw [h i hi,zero_mul,zero_mul])
   _= _:=by rw [dotProduct_smul,dotProduct_transpose_mulVec];rfl
omit G [DecidableEq X][DecidableEq J] in
lemma accepts (c:ℝ)(x:X→ℝ)(v:J→ℝ) : phase K x+heatPay c Q x v=phase (diagStiff c K Q) x - c*(v ⬝ᵥ (Q *ᵥ x)) + c*(v ⬝ᵥ v)/2:= by
 unfold heatPay phase diagStiff; rw [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,← mulVec_mulVec,dotProduct_transpose_mulVec,sub_dotProduct,dotProduct_sub,dotProduct_sub,dotProduct_comm (Q *ᵥ _) v]; simp only [smul_eq_mul]; ring
lemma grade {x:X→ℝ}(v:J→ℝ)(h:StripQ a x): phase K (x+D *ᵥ v)+heatPay c Q (x+D *ᵥ v) v=phase L v + phase (diagStiff c K Q) x:=by
 let t:=D *ᵥ v; let R:=diagStiff c K Q
 have he:= G.eye h v; have hs:= G.eye (G.clipped v) v
 have hv:v ⬝ᵥ (L *ᵥ v)=c*(v ⬝ᵥ v - v ⬝ᵥ (Q *ᵥ t)):=by rw [← G.stiff, smul_mulVec,sub_mulVec,one_mulVec, dotProduct_smul, dotProduct_sub, ← mulVec_mulVec v Q D];rfl
 have hh:t ⬝ᵥ (R *ᵥ x)= x ⬝ᵥ (R *ᵥ t):=by rw (occs:=.pos [1])[← show R.transpose=R from G.style]; rw [dotProduct_transpose_mulVec]
 rw [accepts];change phase R (x+t)-_+_= _
 simp_rw [phase, Matrix.mulVec_add, dotProduct_add,add_dotProduct]
 rw [hh,show x ⬝ᵥ _=_ from he,show t ⬝ᵥ (R *ᵥ t)= _ from hs,hv]; unfold t;ring
-- Right inverse fees eq with active rows; yields precision inversion on actual slice affine variables.
lemma output (i j:X)(h:a j) : (diagStiff c K Q *ᵥ N.transpose i) j = (Pi.single i (1:ℝ):X→ℝ) j:= by
 apply Eq.trans (_root_.id (α:=((diagStiff c K Q *ᵥ N.transpose i) j=(1:Matrix X X ℝ) j i)) (G.fees j i h)); simp [Pi.single_apply,Matrix.one_apply,eq_comm]
lemma alive (j:X) : StripQ a (N.transpose j):= fun _ h=> G.inverse _ _ h
end GridQ

variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]



def joint (R:Matrix X X ℝ)(T:E →ₗ[ℝ] (X→ℝ)): E→ₗ[ℝ] Module.Dual ℝ E where
 toFun x:= {
    toFun:= fun y=>T y ⬝ᵥ (R*ᵥ T x)
    map_add' y z:=by rw [map_add,add_dotProduct]
    map_smul' r y:= by rw [map_smul,smul_dotProduct];rfl }
 map_add' x y:=by
    ext1 b; change T b ⬝ᵥ (R *ᵥ T (x+y))= T b ⬝ᵥ (R *ᵥ T x)+ T b ⬝ᵥ (R *ᵥ T y)
    rw [map_add,mulVec_add,dotProduct_add]
 map_smul' r x:=by
    ext1 b; change T b ⬝ᵥ (R*ᵥ T (r • x))= r • (T b ⬝ᵥ (R*ᵥ T x)); rw [map_smul,mulVec_smul,dotProduct_smul]

variable (T:E →ₗ[ℝ] (X→ℝ))(R : Matrix X X ℝ)
variable (h: R.transpose=R)

variable [FiniteDimensional ℝ E] (hc:∀ x,x≠0→0<phase R (T x))
omit [DecidableEq X] in
lemma phase_cont : Continuous (fun x=>T x ⬝ᵥ (R*ᵥ T x)):= by
 unfold mulVec dotProduct; have ht:= T.continuous_of_finiteDimensional; fun_prop
omit [DecidableEq X] [FiniteDimensional ℝ E] in
lemma phase_scale (r:ℝ)(x:E):phase R (T (r • x))=r^2*phase R (T x):= by unfold phase; rw [map_smul,mulVec_smul,smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; ring
include hc
omit [DecidableEq X] in
lemma literal : ∃ s>0,∀ x:E, s*‖x‖^2≤ phase R (T x):=by
 have hh : ∃ c>0, ∀ x∈sphere (0:E) 1,c≤ phase R (T x):= by
    haveI : ProperSpace E := FiniteDimensional.proper ℝ E
    by_cases h : (sphere (0:E) 1).Nonempty
    · obtain ⟨x,hx,h'⟩:= (isCompact_sphere ..).exists_isMinOn h (((phase_cont T R).div_const 2).continuousOn); exact ⟨_,hc x (by intro ht; rw [ht] at hx; simp at hx),fun _ hx=>h' hx⟩
    exact ⟨1,zero_lt_one,fun x hx=> (h ⟨_,hx⟩).elim⟩
 obtain ⟨c,hc,h'⟩:=hh; refine ⟨c,hc,?_⟩; intro x; by_cases h:x=0
 · subst x; simp [phase]
 have hx:0<‖x‖:= norm_pos_iff.mpr h; let v:= ‖x‖⁻¹ • x; have hp : ‖x‖ • v=x:= by unfold v; rw [smul_smul,mul_inv_cancel₀ hx.ne',one_smul]
 rw [mul_comm c, ← show phase R (T (‖x‖ • v))=phase R (T x) from (by rw [hp]), phase_scale]; gcongr; apply h' v; simp [v,norm_smul,hx.ne']

omit hc
def nymph : Law E:={
 P:=joint R T
 turns x y:=by
    change T y ⬝ᵥ (R*ᵥ T x)= T x ⬝ᵥ (R *ᵥ T y)
    rw (occs:=.pos [1])[← h]; rw [dotProduct_transpose_mulVec]
 slope:=literal T R hc
 smooth:=phase_cont T R }
-- resolve inverse line directly
variable {T}
def wing (T:E→ₗ[ℝ] (X→ℝ))(i:X) : Module.Dual ℝ E:= (LinearMap.proj i).comp T
namespace GridQ
variable (G:GridQ c a K L Q D N)
variable (hb:∀ x:E,x≠0→0<phase (diagStiff c K Q) (T x))
variable (hT:∀ x,StripQ a (T x)) (he:∀ j:X,∃ y,T y=N.transpose j)
include hT he
lemma wickN (i j) : (nymph T (diagStiff c K Q) G.style hb).wick (wing T i) (wing T j)= N j i:= by
 let A:= nymph T (diagStiff c K Q) G.style hb; let R:= diagStiff c K Q
 obtain ⟨y,hy⟩:= he i; have hY : A.P y=wing T i:=by
    ext1 x; change T x ⬝ᵥ (R *ᵥ T y)= T x i; rw [hy,← dotProduct_single_one (T x) i]; apply Finset.sum_congr rfl; intro j _; by_cases h:a j
    · rw [show _=_ from G.output i j h]
    rw [hT x j h,zero_mul,zero_mul]
 change (wing T j) (A.inverse (wing T i))=N j i; rw [← hY, Law.solves]; exact congr_fun hy j
end GridQ
end YM.RegulatorIR.Quadratic
