import YM.WilsonBridge.Deproject
/-!
# Exact restriction of unfixed vertices to orbit chart

Part one: usual based action vs Landau, prescribed half factor, paint of mean-zero
site field plus the rotation correction. Actual coupling powers applied afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Injections
open MS MS.Book MS.Koszul MS.City MS.Native MS.Tone MS.Plane Lattice MS.Orbit MS.Landau MS.Bare MS.Cylinder MS.Swirl
open Function Finset Full Based Based.Position Taylor Filter PertExtension Orb
open scoped BigOperators Matrix Topology Matrix.Norms.Frobenius ContDiff
variable {I A:Type} [Fintype I] [Fintype A]{G:Gauge}{n:Side}
local notation "GJ" => Position.Gluon G n
local notation "GC" => Position.Ghost G n
local notation "π"=> Position.Parity G n
local notation "L"=> Position.Letter G n
local notation "Pₑ"=> Position.E G n
local notation "V"=> Full.Index G n
local notation "J"=> Full.Glu G n
local notation "C"=> Full.Ghost G n
local notation "T"=> aFull G n
local notation "η"=> liftA G n
local notation "Uₐ"=> Ux G n
local notation "Ω"=> cLift G n
local notation "χ"=> Native.Chart.drive n
local notation "ν"=> Native.direction ( P:=Site n ) ( G:=G )
local notation "Λ"=> Bare.Focus.Glow.e0 ( Position.glow G n )
local notation "Λₐ"=> Λe G n
local notation "Λς"=> Λc G n
local notation "αλ"=>alphabet G n
local notation "pu"=> σbranch ( G:=G ) ( n:=n )
local notation "χo"=> Native.Chart.loco ( Native.Chart.drive n )
local notation "χν"=> Native.Chart.roam ( Native.Chart.drive n )
local notation "Θp"=> Θ G n
local infixr:70 " ⋆"=> product π
local infixr:70 " ✤"=> product pu
local notation "W" => Lab.docket n ( Native.Wilsonian.W G )
local notation "H" => Lab.docket n ( Native.Wilsonian.H G )
local notation "YK" => (Position.glow G n)
local notation "Yf" => (Native.glow G (Site n))
local notation "TΒ" => Native.Paper G (Site n)
local notation "Xf" => panel G (Site n)
local notation "TΓ" => Position.Bracket G n
local notation "Φ" => pull Uₐ
local notation "αa[" i "]" => atLetter (Based.a i) (A:=L) (R:=ℂ)
local notation "αk[" i "]" => atLetter (Based.k i) (A:=L) (R:=ℂ)
local notation "αc[" i "]" => atLetter (Based.c i) (A:=L) (R:=ℂ)
local notation "αb[" i "]" => atLetter (Based.b i) (A:=L) (R:=ℂ)
lemma lists {R:Type}[AddCommMonoid R](X: Letters J C→R): ∑ i,X i=(∑ i,X (Based.a i))+(∑ i,X (Based.c i))+((∑ i,X (Based.k i))+(∑ i,X (Based.b i))):= counting X
lemma lists_b {R:Type}[AddCommMonoid R](X: L→R): ∑ i,X i=(∑ i,X (Based.a i))+(∑ i,X (Based.c i))+((∑ i,X (Based.k i))+(∑ i,X (Based.b i))):= by rw [Fintype.sum_sum_type]; simp [Fintype.sum_sum_type]
local notation "Foo" => diagM (Λe G n) (Λe G n) (Λc G n) 0
lemma U_c (i:C): Φ (atLetter (Full.c i))=∑ j:GC, Λς i j • αc[j]:= by rw [pull_letter, ← alph_c, lists_b]; simp_rw [at_Ux]; simp [diagM,Based.a,Based.b,Based.c,Based.k]
lemma U_k (i:J): Φ (atLetter (Full.k i))=∑ j:GJ, Λₐ i j • αk[j]:= by rw [pull_letter, ← alph_k, lists_b]; simp_rw [at_Ux]; simp [diagM,Based.a,Based.b,Based.c,Based.k]
lemma U_b (i:C): Φ (atLetter (Full.b i))=0:= by rw [pull_letter,← alph_b,lists_b]; simp_rw [at_Ux]; simp [diagM,Based.a,Based.b,Based.c,Based.k]

lemma upKnot (i:J) (z:GC) (he:Even n.val):
    ∑ j:C, Λς j z • (Φ (ink ν (projector i ∘ χo j)))=ink Λ (projector i ∘ η ∘ flow z):= by
    let A (j:C) (x:T):= projector i (χo j x); have hu j: germ (projector i ∘ χo j):= (projector i).contDiff.contDiffAt.comp 0 (Native.Chart.ride _ j)
    let MM:= (liftA G n).toContinuousLinearMap
    have hv j: germ ((projector i ∘ χo j) ∘ (η)):= by refine ContDiffAt.comp (f:=⇑MM) (g:=projector i ∘ χo j) (0:Pₑ) ?_ MM.contDiff.contDiffAt; rw [map_zero]; exact hu _
    simp_rw [pigment (hu _),Λc,entry, ← ink_smul Λ (hv _), ← ink_sum Λ univ ( F:=fun j=> projector j (Ω (priv z)) • ((projector i ∘ χo j) ∘ η) ) ( fun j _=> ( hv j ).const_smul ( projector j (Ω (priv z)) ) ) ]; apply inkit
    filter_upwards [painted_flow he z] with f h
    rw [Finset.sum_apply]; change ∑ j:C,projector j (Ω (priv z)) • projector i ( χν (η f) (priv j) )=projector i (η (flow z f)); rw [← h]; conv_rhs=> rw [← Native.frame (Ω (priv z)),map_sum,map_sum]
    simp_rw [map_smul]
lemma stoneU (i:J)(he:Even n.val): Φ (Focus.stone Yf χo i)=∑ z:GC, αc[z] ⋆ ink Λ (projector i ∘ η ∘ flow z):= by
    change Φ (∑ q:C,atLetter (Full.c q) ✤ ink ν ( projector i ∘ χo q ))=_; simp_rw [map_sum, pull_prod Uₐ transports, U_c,map_sum, LinearMap.sum_apply,map_smul,LinearMap.smul_apply ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun j _=>?_); rw [← upKnot i j he, map_sum ]; simp_rw [map_smul]
-- push E^t proof. E^t E = 2
lemma by_half (X:Pₑ)(i:GJ) (he:Even n.val): ∑ j:J,glyph (liftA G n) j i * projector j (η X)=(2:ℝ)*projector i X:= by
    let U : Matrix GJ GJ ℝ:= (glyph η).transpose*glyph η; let Z:Matrix GJ GJ ℂ:= (Λe G n).transpose *Λe G n
    have hz (k b:GJ) : (U k b:ℂ)= ((1:Matrix GJ GJ ℝ) k b + (1:Matrix GJ GJ ℝ) k b:ℝ):= by
       rw [show (↑(U k b):ℂ)= Z k b from ?_, show Z = 1+1 from eigenA he ]; · by_cases h:k=b<;> simp [Matrix.one_apply,h]
       unfold Z U; rw [Matrix.mul_apply,Matrix.mul_apply]; push_cast; rfl
    have hh (k b:GJ) : U k b= if k=b then 2 else 0:= by apply Complex.ofReal_injective; push_cast at hz; rw [ hz ]; by_cases h:k=b<;> norm_num [h,Matrix.one_apply]
    have ht : ∑ j:J,glyph η j i * projector j (η X)= ∑ j:J,glyph η j i * ∑ k:GJ,glyph η j k* projector k X:= by
        apply Finset.sum_congr rfl; intro j _; congr 1
        nth_rw 1 [ ← Native.frame X ]; rw [map_sum,map_sum]; simp_rw [map_smul]; apply Finset.sum_congr rfl; intro k _; exact mul_comm ..
    rw [ht]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [ ← mul_assoc, ← Finset.sum_mul ]; change ∑ k:GJ, U i k*projector k X=_; simp_rw [hh]; simp [ite_mul]
lemma with_E (he:Even n.val)(z:GJ)(a:GC): ∑ i:J, Λₐ i z • ink Λ (projector i ∘ η ∘ flow a)= (2:ℂ) • ink Λ (projector z ∘ flow a):= by
    have hp (j:J): germ (projector j ∘ η ∘ flow a):= (projector j).contDiff.contDiffAt.comp 0 ((η).toContinuousLinearMap.contDiff.contDiffAt.comp ( f:=flow a ) 0 (drift_priced a))
    have hv : germ (projector z ∘ flow a):= (projector z).contDiff.contDiffAt.comp 0 (drift_priced a); have hz : ∀ i:J, Λₐ i z=(glyph η i z:ℂ):= fun _=>rfl; simp_rw [hz,← ink_smul Λ ( hp _ ), ←ink_sum Λ univ (F:=fun i=>(glyph η i z) • (projector i ∘ η ∘ flow a)) (fun i _=> ( hp i ).const_smul (glyph η i z)) ]; rw [← Complex.ofReal_ofNat (n:=2),← ink_smul Λ hv ]; apply congr_arg; funext i; rw [Finset.sum_apply]; exact by_half _ _ he
lemma αstone (he:Even n.val)(z:GJ): ∑ i:J, Λₐ i z • Φ (Focus.stone Yf χo i)=(2:ℂ) • Focus.stone (YK) flow z:= by
    change _=(2:ℂ) • ∑ i:GC,αc[i] ⋆ ink Λ (projector z ∘ flow i); simp_rw [ stoneU _ he, Finset.smul_sum ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_; rw [← map_smul,← with_E he z i,map_sum ]; simp_rw [map_smul]
lemma hungU (he:Even n.val): Φ ( (TΒ).hung ( Focus.launch Yf (colorTerm G (Site n)) χo ) )=(2:ℂ) • ∑ i:GJ,αk[i] ⋆ Focus.stone (YK) flow i:= by
    let B:= Focus.launch Yf (colorTerm G (Site n)) χo; unfold Bonded.hung; rw [ ( Xf ).split_i ]; change Φ ( (∑ i:J,(1:ℂ) • (atLetter (Full.k i) ✤ B (( Xf ).AId i)))+( ∑ j:C, (-(1:ℂ)) • (atLetter (Full.b j) ✤ B (( Xf ).KId j)) ) )=_; unfold B; simp_rw [one_smul, Focus.launch_stone,map_add,map_sum,map_smul,pull_prod Uₐ transports,U_b,U_k,map_zero, LinearMap.zero_apply,smul_zero, Finset.sum_const_zero,add_zero,map_sum,map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← map_smul, ← αstone he i,map_sum]; simp_rw [map_smul]
-- FULL material. differs in antighost projections yet
abbrev paintW (G:Gauge)(n:Side) : Raw (Position.Letter G n) ℂ:= ink (Position.glow G n).e0 (exponent G n)+ ∑ i:Position.Gluon G n,product ( Position.Parity G n ) (atLetter (Based.k i)) (Focus.stone (Position.glow G n) flow i)
lemma wholeU (he:Even n.val): Φ ( W )=(2:ℂ) • paintW G n:= by
    rw [Native.Wilsonian.witnessD n, Focus.Sourced,map_add, hungU he]; change Φ ( ink ν (Native.Chart.rent χ) ) + _= _; rw [ pigment (Native.Chart.rent_s _),actually_rent, ink_smul _ (expGerm G n),Complex.ofReal_ofNat ]; exact (smul_add ..).symm
lemma haarU (he:Even n.val): Φ H = (2:ℂ) • Position.haarW G n:= by
    rw [ Native.Wilsonian.shiftD ]; change Φ (ink ν Native.Chart.totalH)=_; rw [pigment Native.Chart.nice_totalH, inkit Λ (haar_full he), ink_smul _ Position.haarSmooth ]; norm_num; rfl
end YM.WilsonBridge.Injections
