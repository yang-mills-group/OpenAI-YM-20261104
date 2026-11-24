import YM.MS.Cylinder.Blend
import YM.MS.RulesBV

/-!
# From finite Lie-vector data to S

J are link variables; W, DF ordinary directions. K are gauge parameters, any
   aliases in site maps already transported. Color/fermionic parity separated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare
open Function Filter Finset Set Koszul Cylinder Taylor
open scoped Topology ContDiff
variable {A I J K: Type*} {p:Sector A} {B:Bonded p I}

structure Focus {p:Sector A} (B:Bonded p I)(J K:Type*) where
    call : (J⊕K)≃I
    act i: p (B.plain (call (Sum.inl i)))=false
    gauge j : p (B.plain (call (Sum.inr j)))=true
namespace Focus
variable (X:Focus B J K)
abbrev AId (i:J): I:= X.call (Sum.inl i)
abbrev KId (k:K): I:= X.call (Sum.inr k)
def spark (v:K): Raw A ℂ:= atLetter (B.plain (X.KId v))
lemma spark_p (v:K): Pure p true (X.spark v):= X.gauge v ▸ speaks_p (B.plain (X.KId v)) -- p cast orientation
lemma spark_s (v:K): Symm p (X.spark v):= speaks_s _
lemma spark_dual (v:K)(i:I): D (B.dual i) (X.spark v)=0:= unheard _ (B.diff (X.KId v) _).symm
lemma spark_never (v:K)(i:J): D (B.plain (X.AId i)) (X.spark v)=0:= unheard _ (fun h=> Sum.inl_ne_inr (X.call.injective (B.plain.injective h)))
lemma spark_me (v:K) : D (B.plain (X.KId v)) (X.spark v)=coin 1:= hear _
lemma spark_far (v:K){u:K}(h:u≠v): D (B.plain (X.KId u)) (X.spark v)=0:= unheard _ (fun hv=> h (Sum.inr.inj (X.call.injective (B.plain.injective hv))))

variable [Fintype I][Fintype J][Fintype K]
lemma split_i {T:Type*}[AddCommMonoid T](f:I→T): ∑ i:I,f i= (∑ i:J,f (X.AId i))+(∑ j:K,f (X.KId j)):= by rw [← Equiv.sum_comp X.call f, Fintype.sum_sum_type] -- possible rfl automatically
omit [Fintype I] [Fintype J] [Fintype K] in
lemma pick (P:I→Prop)(hp:∀ i:J,P (X.AId i))(hp':∀ j:K,P (X.KId j)): ∀ i,P i:= by
    intro i; obtain ⟨k|k,rfl⟩:=X.call.surjective i; exact hp k; exact hp' k

variable {E: Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
structure Glow (X:Focus B J K) (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E] where
   e0 : A→E
   seed (j:J) : E→L[ℝ] ℝ
   restore (v:E): ∑ i:J, seed i v • e0 (B.plain (X.AId i))=v
   ever i: e0 i≠0→ ∃ j,i=B.plain (X.AId j)

namespace Glow
variable {X}
variable (γ: Glow X E)
omit [Fintype I] [Fintype K] in
lemma spark_off (i:K): γ.e0 (B.plain (X.KId i))=0:= by by_contra h; obtain ⟨w,hw⟩:= γ.ever _ h; exact Sum.inl_ne_inr (X.call.injective (B.plain.injective hw)).symm
omit [Fintype I] [Fintype K] in
lemma never (i:A): p i=true→ γ.e0 i=0:= by intro ha; by_contra h; obtain ⟨w,rfl⟩:= γ.ever _ h; simp only [show p (B.plain (X.AId _))= _ from X.act w] at ha; contradiction
omit [Fintype I] [Fintype K] in
lemma dual_off (i:I): γ.e0 (B.dual i)=0:= by by_contra h; obtain ⟨w,hw⟩:= γ.ever _ h; exact B.diff _ _ hw.symm
end Glow

section S
variable {X} (Y: Glow X E) (τ:K→K→K→ℝ) (V:K→ E→E)
local notation "μ"=> product p
local notation "ψ"=> ink Y.e0
local notation "W" =>Raw A ℂ
local notation "L"=> X.spark
def stone (j:J): Raw A ℂ:= ∑ k:K, μ (X.spark k) (ψ (Y.seed j ∘ V k))
variable (X) in
def shadow (i:K): W:=∑ a:K,∑ b:K,(-(τ a b i:ℂ)/2) • product p (X.spark a) (X.spark b)
-- p hygienic issue in binder above? notation W uses section p? W only A.
def launch (i:I): Raw A ℂ := Sum.elim (stone Y V) (shadow X τ) (X.call.symm i) -- args lint
omit [Fintype I] in
lemma launch_stone (i:J): launch Y τ V (X.AId i)=stone Y V i:= by simp [launch,AId]
omit [Fintype I] in
lemma launch_shadow (i:K): launch Y τ V (X.KId i)=shadow X τ i:=by simp [launch,KId]
omit [Fintype I] in
lemma lifting (h:∀ i,germ (V i)): B.Lifted (launch Y τ V) where
    flip:=X.pick _ (fun i=> by
       rw [launch_stone, show p (B.dual (X.AId i))=true by
          have he := B.wave (X.AId i); rw [show p (B.plain (X.AId i))=false from X.act i] at he; cases hv:p (B.dual (X.AId i)) <;> simp_all]; exact Pure.sum _ (fun j _=> (X.spark_p j).prod (ink_p _ Y.never _)))
     (fun i=> by
       rw [launch_shadow,show p (B.dual (X.KId i))=false by have he := B.wave (X.KId i); rw [show p (B.plain (X.KId i))=true from X.gauge i] at he; cases hv:p (B.dual (X.KId i)) <;> simp_all]; exact Pure.sum _ (fun k _=> Pure.sum _ fun j _=> ((X.spark_p k).prod (X.spark_p j)).smul _))
    sym:= X.pick _ (fun i=> by rw [launch_stone]; exact Symm.sum _ fun j _=> (X.spark_s j).times (ink_s _ Y.never ((Y.seed i).contDiff.contDiffAt.comp 0 (h j))))
            (fun i=>by rw [launch_shadow]; exact Symm.sum _ fun k _=> Symm.sum _ fun j _=> ((X.spark_s k).times (X.spark_s j)).smul _)
    qonly i:=X.pick _ (fun i=>by simp [launch_stone,stone,D_product,Y.dual_off,ink_off,spark_dual])
              (fun i=>by simp [launch_shadow,shadow,D_product,spark_dual])
-- realizes vector
abbrev S: Op A ℂ:= B.glory (launch Y τ V)
omit [Fintype I] [Fintype K] in
lemma push_stone (f:E→ℝ)(k:K)(a:E): (fderiv ℝ f a) (V k a)=∑ j:J,(Y.seed j ∘ V k) a * layer (Y.e0 (B.plain (X.AId j))) f a:= by nth_rw 1 [← Y.restore (V k a)]; simp only [map_sum,map_smul]; rfl
def rotate (Z:E→E)(F:E→ℝ)(a:E) := fderiv ℝ F a (Z a)
lemma cast_ink {f:E→ℝ}(hf:germ f)(h:∀ i,germ (V i)): S Y τ V (ψ f)=∑ k:K,μ (L k) (ψ (rotate (V k) f)):= by
    rw [Bonded.reveals,X.split_i]; simp only [ink_off _ (Y.spark_off _),launch_stone,map_zero,Finset.sum_const_zero,add_zero,stone,map_sum,LinearMap.sum_apply,inktip]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
    let F (i:J) := (Y.seed i ∘ V k); let q (i:J) := layer (Y.e0 (B.plain (X.AId i))) f; have hh i : germ (F i) := ((Y.seed i).contDiff.contDiffAt.comp 0 (h k)); have hq i : germ (q i) := germ_layer hf _
    rw [show rotate (V k) f=∑ i:J,F i*q i by ext a; rw [Finset.sum_apply]; exact push_stone Y V f k a, ink_sum _ _ (fun i _=> show germ (F i*q i) from (hh i).mul (hq i)),map_sum]; simp_rw [ink_mul Y.e0 Y.never (hh _) (hq _), ← times_assoc]; rfl
end S
end Focus
end YM.MS.Bare
