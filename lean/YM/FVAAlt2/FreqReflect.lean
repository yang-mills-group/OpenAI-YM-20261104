import YM.FVAAlt2.Planes

/-! Fourier lift of range and equivariance predicates to position space. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Finset Matrix Lattice Function MS MS.Koszul MS.Plane MS.Landau MS.Cylinder MS.Tone MS.Native
open MS.Orbit MS.Orbit.Cog MS.Swirl MS.Swirl.Near
variable {G:Gauge}{n:Side}
local notation "A" => Mode G n
local notation "C" => QuotK G n
local notation "Z" => Site n
local notation "F" => fourier G n
local notation "ℐ" => Complex.I

structure OKPosition {R:Type}[AddCommGroup R](n:Side){G:Gauge}(u:Mode G n→R) : Prop where
  noHarm (t:Branch G Axis): ∑ x, u (t,x)=0
  vector (k:G.ColorIndex)(x:Site n): ∑ i, (u (vecBranch k i,x)-u (vecBranch k i,x-step i))=0
  gradient : ∃ v:G.ColorIndex → Site n→R, ∀ k x i, u (kBranch k i,x)=v k x-v k (x+step i)
  noB (k:G.ColorIndex)(x:Site n): u (bBranch k,x)=0

def tensorMir {R:Type}[AddCommGroup R](u:A→R) (b:Branch G Axis)(x:Site n) : R:= match b.1.1 with
  | none=> u (b,-x)
  | some i=> -u (b,-x-step i)
def mirrored {R:Type}[AddCommGroup R](u:A→R):Prop:= ∀ b x,tensorMir u b x=u (b,x)

def sampleWave (f:Z→ℂ) (x:Z):ℂ:= ∑ p, Bloch.cell p x*f p
lemma wave_bijective : Bijective (sampleWave (n:=n)) := by
  let L:= Matrix.mulVecLin ((Bloch.F n).transpose)
  have he: L.toFun=sampleWave (n:=n):=rfl
  rw [← he]; let b:=((n.val:ℂ)^4)⁻¹; let U: Matrix Z Z ℂ:= b • star (Bloch.F n); have hu: U* Bloch.F n=1:= by rw [smul_mul_assoc,Bloch.coGram,smul_smul,show b*(n.val:ℂ)^4=1 from _root_.inv_mul_cancel₀ (pow_ne_zero _ (Bloch.side_ne n)),one_smul]
  have hv: U.transpose * (Bloch.F n).transpose=1:= by rw [← Matrix.transpose_mul,mul_eq_one_comm.mp hu,Matrix.transpose_one]
  have ht:Injective L:= LeftInverse.injective (g:= (Matrix.mulVecLin U.transpose)) fun x=> show _ *ᵥ (_ *ᵥ _) = _ from (by rw [Matrix.mulVec_mulVec,hv,Matrix.one_mulVec])
  exact ⟨ht,LinearMap.surjective_of_injective ht⟩

lemma sample (f:A→ℂ)(b:Branch G Axis)(x:Z): ((F).transpose *ᵥ f) (b,x)= sampleWave (fun p=> f (b,p)) x:=by
  simp_rw [Matrix.mulVec,dotProduct,Fintype.sum_prod_type (α₁:=Branch G Axis) (α₂:=Site n)]
  rw [Finset.sum_eq_single b]; simp only [transpose_apply,fourier_on]; rfl
  · intro a _ he; simp [fourier_off he]
  simp

lemma sample_δ (f:Z→ℂ)(x y:Z): sampleWave f x-sampleWave f (x+y)= sampleWave (fun p=> (1-Bloch.cell p y)*f p) x:= by
  unfold sampleWave; rw [← sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [Bloch.cell_add]; ring
lemma sample_sum (f:Z→ℂ): ∑ x,sampleWave f x= brightness n * f 0 := by
  unfold sampleWave; rw [Finset.sum_comm,sum_eq_single 0]; simp [Bloch.cell, recVol]
  · intro b _ h; rw [← sum_mul,Bloch.sum_cell h]; simp
  simp

lemma sample_zero (f:Z→ℂ): sampleWave f=0 ↔ f=0 := by
  have h: sampleWave (0:Z→ℂ)=0:= funext (fun x=>by simp [sampleWave])
  exact ⟨fun hv=> wave_bijective.1 (hv.trans h.symm),fun he=>he ▸ h⟩
lemma sample_div (f:A→ℂ)(x:Z)(k:G.ColorIndex): ∑ i,(((F).transpose *ᵥ f) (vecBranch k i,x)-((F).transpose *ᵥ f) (vecBranch k i,x-step i))=
    sampleWave (fun p=> ℐ * ∑ i:Axis, kin p i*((amp p i)⁻¹ * f (vecBranch k i,p))) x:= by
  simp_rw [sample]; simp_rw [sub_eq_add_neg x, sample_δ]; unfold sampleWave; rw [Finset.sum_comm]; refine sum_congr rfl fun p _=>?_ ; simp_rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [kn_opp]; ring

lemma sample_range (f:A→ℂ): OKFreq n f↔ OKPosition n ((F).transpose *ᵥ f):= by
 constructor
 · intro H; refine ⟨fun t=>?_, fun k x=> ?_, ?_,fun k p=>?_⟩
   · simp_rw [sample]; rw [sample_sum]; rw [H.noHarm,mul_zero]
   · simp_rw [sample_div,H.vector,sampleWave]; simp
   · obtain ⟨g,hg⟩:= H.gradient; refine ⟨fun k=> sampleWave (g k),fun k x i=> ?_⟩; rw [sample,sample_δ]; simp only [hg]
   rw [sample]; simp [H.noB,sampleWave]
 intro H; let U:=(F).transpose *ᵥ f; refine ⟨fun t=> ?_,fun k p=> ?_, ?_,fun k p=>?_⟩
 · obtain he:=H.noHarm t; simp_rw [sample] at he; rw [sample_sum] at he; exact (mul_eq_zero.mp he).resolve_left (right_ne_zero_of_mul (by rw [lightW]; exact one_ne_zero : scaleZ n * brightness n≠0))
 · have hv:= H.vector k; simp_rw [sample_div] at hv; exact (mul_eq_zero.mp (congrFun ((sample_zero _).1 (funext hv)) p)).resolve_left Complex.I_ne_zero
 · obtain ⟨g,hg⟩:= H.gradient; choose u hu using fun k:G.ColorIndex=> wave_bijective.2 (g k)
   refine ⟨u,fun k p i=>?_⟩; have he(x:Z): sampleWave (fun p=>f (kBranch k i,p)) x=sampleWave (fun p=> (1-Bloch.cell p (step i))*u k p) x := by rw [← sample,← sample_δ,hu,hg]
   exact congrFun (wave_bijective.1 (funext he)) p
 have he:=H.noB k; simp_rw [sample] at he; exact congrFun ((sample_zero _).1 (funext he)) p

lemma inverse_inj : Injective (fun v:A→ℂ=>(F).transpose *ᵥ v) := by
    intro v u h; funext ⟨b,p⟩; refine congrFun (wave_bijective.1 (a₁:=fun i=>v (b,i)) (a₂:=fun i=>u (b,i)) ?_) p; funext i; rw [← sample, ← sample]; exact congrFun h (b,i)
lemma spin_link (k:G.ColorIndex)(i:Axis)(b:Bool)(p:Site n) :
    (iota G n).spin (((some i,b),k),-p) = -Bloch.cell p (step i) := by
  rw [iota_spin,show switch (addr _) = switch (((some i,b),k),-Coord p) from (switch_pin ((some i,b),k) (ξ_neg p)).symm, switch, show gscore (((some i,b),k),-Coord p)=(-1:ℂ) from rfl, kn_G]
  simp only [lace, neg_neg]; change -1*(amp p i)^2 = _; ring
lemma spin_point (k:G.ColorIndex)(b:Bool)(p:Site n) :
    (iota G n).spin (((none,b),k),p)=1:=by rw [iota_spin,switch,show gscore _=1 from rfl]; simp [lace,flag,weightψ]
lemma cell_reflect (x p:Z): Bloch.cell (-p) (-x) = Bloch.cell p x := by rw [Bloch.cell_inverse,Bloch.cell_duality (-p),Bloch.cell_inverse]; simp [Bloch.cell_duality x p]
lemma mirror_sample (f:A→ℂ)(b:Branch G Axis)(x:Z): tensorMir ((F).transpose *ᵥ f) b x=((F).transpose *ᵥ (mirrorVec (iota G n) f)) (b,x):=by
  unfold tensorMir; rcases b with ⟨⟨_|i,b⟩,k⟩
  · simp only [sample]; unfold sampleWave; conv_lhs=> rw [← Equiv.sum_comp (Equiv.neg Z)]
    apply sum_congr rfl; intro p _; simp [cell_reflect,mirrorVec,iota_mode,spin_point]
  simp only [sample]; unfold sampleWave; rw [← Finset.sum_neg_distrib]; conv_lhs=> rw [← Equiv.sum_comp (Equiv.neg Z)]
  apply sum_congr rfl; intro p _; rw [Equiv.neg_apply, show -x-step i= -(x+step i) from by abel, cell_reflect, Bloch.cell_add]; simp only [mirrorVec,iota_mode,spin_link]; ring

lemma mirror_sampled (f:A→ℂ):mirrorVec (iota G n) f=f ↔ mirrored ((F).transpose *ᵥ f):=by
 refine ⟨fun he b x=>?_,fun ht=>inverse_inj (funext fun ⟨b,x⟩=> (mirror_sample f b x).symm.trans (ht b x))⟩; rw [mirror_sample,he]
end YM.FVAAlt2
