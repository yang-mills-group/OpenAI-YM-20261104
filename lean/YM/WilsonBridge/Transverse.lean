import YM.WilsonBridge.Painted
/-!
# Actual projection cancels the coset correction at transverse A, longitudinal K
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Injections
open MS MS.Book MS.Koszul MS.City MS.Native MS.Tone MS.Plane Lattice MS.Orbit MS.Landau MS.Bare MS.Cylinder MS.Swirl
open Function Finset Based Based.Position Taylor Filter PertExtension Orb
open scoped BigOperators Matrix Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "J"=> Position.Gluon G n
local notation "C"=> Position.Ghost G n
local notation "π"=> Position.Parity G n
local notation "L"=> Position.Letter G n
local notation "T"=> Position.E G n
local notation "Uₐ"=> Ux G n
local notation "Yk"=> Position.glow G n
local notation "Λ"=> Bare.Focus.Glow.e0 ( Position.glow G n )
local notation "Θp"=> Θ G n
local infixr:70 " ⋆"=> product π
local notation "Φ"=> pull Uₐ
local notation "Λp"=> pull ( Θ G n )
local notation "ρ"=> Long G n
local notation "τ"=> Short G n
local notation "So"=> Based.Kinetics.X ( Position.kinetic G n )
local notation "R"=> (Raw ( Position.Letter G n ) ℂ)
local notation "Z"=> paintW G n
local notation "Kα[" i "]"=> atLetter ( Based.k i ) (A:=L) ( «R»:=ℂ )
local notation "Aα[" i "]"=> atLetter ( Based.a i ) (A:=L) ( «R»:=ℂ )
local notation "Cα[" i "]"=> atLetter ( Based.c i ) (A:=L) ( «R»:=ℂ )
-- skew color field.
lemma lifting_color (v:G.Color): symbol (adF v)* So = So * symbol (adF v) := by
    rw [show So = symbol (based (0:T)) from rfl,s_mul,s_mul]; apply congr_arg; apply LinearMap.ext; intro A; funext i
    change G.ad v ( Maurer.volts _ (0:G.Color) )= Maurer.volts _ (0:G.Color)
    simp_rw [Maurer.volt_zero]; rw [map_sub]; have ht x: G.ad v ( liftC G n A x )=liftC G n ( adF v A ) x:= by
       unfold liftC; rw [site_spec,site_spec]; split; · simp
       rfl
    exact congr_arg₂ (fun x y:G.Color=> x-y) (ht _) (ht _)
lemma lifting_trans (v:G.Color): (symbol (adF v ( T':=OEdge n ))).transpose= -symbol (adF v):= by
    ext ⟨i,a⟩ ⟨j,b⟩:1; simp_rw [Matrix.transpose_apply, Matrix.neg_apply,entry,projector_k]; simp only [adF, priv ]; -- pi submaps
    by_cases h:i=j; swap; · simp [h, Ne.symm h]
    subst j; simp only [LinearMap.pi_apply,LinearMap.coe_comp,Function.comp_apply,LinearMap.proj_apply,Pi.single_eq_same] -- simp orientation
    have hh (x:G.Color)(b:Conn G): inner ℝ (Native.baseC b) x=x b:= by rw [← OrthonormalBasis.repr_apply_apply]; simp [Native.baseC]
    rw [← hh,← hh, real_inner_comm (G.ad v _) ]; rw [Gauge.ad_skew, Complex.ofReal_neg]
lemma shorting (he:Even n.val) : τ * So=0:= by rw [Short,Matrix.sub_mul,Long,Matrix.one_mul,Matrix.mul_assoc,shadowProj he,Matrix.mul_one,sub_self]
lemma perp (he:Even n.val)(v:G.Color) : (ρ).transpose * symbol (adF v) * τ=0 := by
   let F:Matrix J J ℂ:= symbol (adF v); have hl : (ρ).transpose=ρ:= ortho he; have hs : (τ).transpose=τ:= by rw [Short,Matrix.transpose_sub,Matrix.transpose_one,hl]
   have hv : τ* F*ρ=0:= by unfold Long; rw [ Matrix.mul_assoc, ← Matrix.mul_assoc F, lifting_color, ← Matrix.mul_assoc ( Short G n ), ← Matrix.mul_assoc τ, shorting he ]; simp -- need F reducibility
   apply_fun Matrix.transpose at hv; rw [Matrix.transpose_mul,Matrix.transpose_mul, show F.transpose= -F from lifting_trans v,hs,Matrix.neg_mul,Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.transpose_zero] at hv; exact neg_eq_zero.mp hv
lemma projK (i:J): Λp Kα[i]= ∑ j:J, ρ i j • Kα[j]:= by rw [pull_letter,lists_b]; simp [Θ, diagM,Based.k, Based.a,Based.c,Based.b ] -- notation test
lemma projA (i:J): Λp Aα[i]= ∑ j:J, τ i j • Aα[j]:= by rw [pull_letter,lists_b]; simp [Θ, diagM,Based.k, Based.a,Based.c,Based.b ]
lemma projB (i:C): Λp (atLetter (Based.b i))=0:= by rw [pull_letter,lists_b]; simp [Θ, diagM,Based.k, Based.a,Based.c,Based.b ]
lemma aloneA (f:T →L[ℝ] ℝ): ink Λ f=∑ i:J,(f (priv i):ℂ) • Aα[i] := by
    suffices H : ink Λ f=∑ i:L,( f ( Λ i ):ℂ ) • atLetter i by
        rw [H,lists_b]; simp_rw [ show ∀ i:C, Λ (Based.c i)=0 from fun _=>rfl, show ∀ i:C, Λ (Based.b i)=0 from fun _=>rfl, show ∀ i:J, Λ (Based.k i)=0 from fun _=>rfl, map_zero ]; simp; rfl
    apply ext_D
    · rw [Finset.sum_apply,Finset.sum_eq_zero]; · rw [drip,map_zero]; rfl
      intro i hi; exact mul_zero _
    intro i; rw [map_sum, Finset.sum_eq_single_of_mem i (mem_univ i)]; swap; · intro k hk ht; rw [map_smul, unheard _ (Ne.symm ht),smul_zero]
    rw [inktip,map_smul,hear, show layer _ f=(fun _=> f (Λ i)) from funext fun y=> DFunLike.congr_fun f.fderiv _, ink_const]; funext l; cases l <;> simp [coin]
-- effect of added generator. leave ∆ GF.
def splash (b:C) : Matrix J J ℂ:= symbol (adF (offsetGhost b))
lemma priceline (b:C)(j:J): ink Λ (projector j ∘ flow b)= ink Λ (projector j∘ generator b)+∑ i:J,splash b j i • Aα[i] := by
    rw [show projector j ∘ flow b= (projector j ∘ generator b )+ (projector j) ∘ adF (offsetGhost b) from funext fun x=> map_add (projector j) _ _, ink_add Λ ((projector j).contDiff.contDiffAt.comp 0 (ongoing b)) ]; swap; · exact ( (projector j).comp (adF (offsetGhost b)).toContinuousLinearMap ).contDiff.contDiffAt
    congr 1; exact aloneA ((projector j).comp ((adF (offsetGhost b)).toContinuousLinearMap)) -- explicit clm
lemma inkC (j:J): Focus.stone (Yk) flow j= Focus.stone (Yk) generator j + ∑ b:C,Cα[b] ⋆ (∑ i:J,splash b j i • Aα[i]) := by
    change (∑ b:C,Cα[b] ⋆ ink Λ (projector j∘ flow b))= (∑ b:C,Cα[b] ⋆ ink Λ (projector j ∘ generator b)) + _; simp_rw [priceline, map_add, Finset.sum_add_distrib]
-- multiply KcA coefficients as Long^t * ad * Short. literal spin independent color. no FP source adj piece.
lemma money (i b:J)(j:C):
      Λp (Kα[i] ⋆ Cα[j] ⋆ (splash j i b • Aα[b]))=∑ a:J,∑ c:J,ρ i a • ((splash j i b) • (τ b c • ( Kα[a] ⋆ Λp Cα[j] ⋆ Aα[c] ))):= by simp only [ pull_prod Θp projection_tie,map_smul,projK,projA,map_sum,LinearMap.sum_apply,LinearMap.smul_apply, Finset.smul_sum ]; rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl fun c _=>?_); rw [smul_comm ( τ b c ), smul_comm (splash j i b)]
lemma bill_moment (b:C) (he:Even n.val) : Λp (∑ i:J,Kα[i] ⋆ (Cα[b] ⋆ (∑ j:J,splash b i j • Aα[j])))=0:= by
    have hp a c: ∑ j:J,∑ i:J,ρ i a * splash b i j * τ j c=(0:ℂ):= by
       simp_rw [ ← Finset.sum_mul ]; change ((ρ).transpose*splash b*τ) a c=0; rw [splash,perp he]; rfl
    have hf (k:J→J→J→J→R): (∑ i:J,∑ j:J,∑ a:J,∑ c:J,k i j a c) = ∑ a:J,∑ c:J,∑ j:J,∑ i:J,k i j a c:= by
       simp_rw [ show ∀ i,(∑ j:J,∑ a:J,∑ c:J,k i j a c)=∑ a:J,∑ c:J,∑ j:J,k i j a c from fun x=> Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _=> Finset.sum_comm)) ]; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun _ _=> Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _=> Finset.sum_comm))
    simp_rw [map_sum,money, smul_smul, ← mul_assoc ]; rw [ hf ( fun i j a c=> ( ρ i a * splash b i j * τ j c ) • ( Kα[a] ⋆ Λp Cα[b] ⋆ Aα[c] ) ) ]; simp_rw [ ← Finset.sum_smul,hp ]; simp
lemma checked_p (he:Even n.val): Λp Z= Λp (Position.actionW G n):= by
    let B:= colorTerm G (BasedSite n); unfold Position.actionW Focus.Sourced Bonded.hung; rw [ ( Position.focus G n ).split_i ];
    change Λp ( ink Λ (exponent G n) + (∑ i:J,Kα[i] ⋆ Focus.stone (Yk) flow i) ) = Λp ( ink Λ ( exponent G n ) + ( (∑ i:J,(1:ℂ) • (Kα[i] ⋆ Focus.stone (Yk) generator i))+( ∑ j:C, (-(1:ℂ)) • (atLetter (Based.b j) ⋆ Focus.shadow (Position.focus G n) B j)) ) )
    simp_rw [inkC,map_add,one_smul,Finset.sum_add_distrib,map_sum,map_smul,pull_prod Θp projection_tie (atLetter (Based.b _)), projB,map_zero,LinearMap.zero_apply,smul_zero, Finset.sum_const_zero,add_zero ]; suffices (∑ i:J,∑ j:C,Λp (Kα[i] ⋆ ( Cα[j] ⋆ (∑ b:J,splash j i b • Aα[b]))))=0 by simp_rw [map_add,map_sum,map_smul]; simp_rw [map_sum,map_smul] at this; rw [ this,add_zero]
    rw [Finset.sum_comm]; exact Finset.sum_eq_zero (fun i _=> by simp_rw [← map_sum]; exact bill_moment i he) -- metavariable binding
end YM.WilsonBridge.Injections
