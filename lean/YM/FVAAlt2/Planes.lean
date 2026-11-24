import YM.FVAAlt2.Line

/-! Exact range of the torus and quotient propagator before inserting fields.
We include exactly which harmonic conventions are enforced. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Finset Matrix Lattice Function MS MS.Koszul MS.Plane MS.Landau MS.Cylinder MS.Tone MS.Native
open MS.Orbit MS.Orbit.Cog MS.Swirl MS.Swirl.Near
variable {G:Gauge}{n:Side}
local notation "A" => Mode G n
local notation "M" => VacuumK G n
local notation "S" => Site n
local notation "C" => G.ColorIndex
local notation "ℐ" => Complex.I

structure OKFreq (n:Side){G:Gauge}(u:Mode G n→ℂ) : Prop where
  noHarm (t:Branch G Axis): u (t,0)=0
  vector (k:G.ColorIndex)(p:Site n): ∑ i, kin p i * ((amp p i)⁻¹ * u (vecBranch k i,p))=0
  gradient : ∃ v:G.ColorIndex → Site n→ℂ, ∀ k p i, u (kBranch k i,p)=(1-Bloch.cell p (step i)) * v k p
  noB (k:G.ColorIndex)(p:Site n): u (bBranch k,p)=0

lemma no_zero (b:Branch G Axis)(u:A→ℂ): (M *ᵥ u) (b,0)=0:= by
  have he: ell (0:S)=0:=by simp [ell,Wave_zero,Momentum.sq]
  rcases b with ⟨⟨_|i,_|_⟩,k⟩
  · rw [row_c]; simp [he]
  · rw [row_b]
  · rw [row_A]; simp [he]
  rw [row_K]; simp [he]

lemma ordinary_image (u:A→ℂ): OKFreq n (M *ᵥ u) where
  noHarm b := no_zero b u
  vector k p:= by
     simp_rw [row_A]; let y i:= (amp p i)⁻¹ * u (vecBranch k i, -p)
     let f i:= ∑ j, oprec p i j*y j
     let v:=normK n / ell p^2
     have he(i:Axis): kin p i*((amp p i)⁻¹*((normK n * amp p i / ell p^2)* f i))= v * (kin p i * f i):=by unfold v; rw [show normK n * amp p i / ell p ^ 2=amp p i*(normK n / ell p^2) from by ring, mul_assoc (amp p i),_root_.inv_mul_cancel_left₀ (nonz _ _)]; ring
     change (∑ i:Axis, kin p i*((amp p i)⁻¹*((normK n * amp p i / ell p^2) * f i)))=0; simp_rw [he, ← Finset.mul_sum]; rw [show (∑ i, kin p i * f i)=0 from kn_vecCancel p y,mul_zero]
  gradient := ⟨fun k p=> -normK n/ell p*u (cBranch k,-p),fun k p i=> by
     rw [row_K,show 1-Bloch.cell p (step i)= -(amp p i*(ℐ*kin p i)) from (by rw [← kn_diff,neg_sub])]; ring⟩
  noB := fun k p=> row_b p k u

def voltInverse (u:A→ℂ)(f:C→S→ℂ) : Mode G n→ℂ
 | (((some i,false),k),p) => ell (-p) / normK n * u (vecBranch k i,-p)
 | (((none,false),k),p) => -ell (-p)/normK n*f k (-p)
 | (((some i,true),k),p)=> amp (-p) i * (kin (-p) i*(u (cBranch k,-p)/(normK n*ℐ)))
 | (((none,true),_),_)=>0

lemma all_image {u:A→ℂ}(H: OKFreq n u): ∃ f:A→ℂ,M *ᵥ f=u:=by
 obtain ⟨a,ha⟩:= H.gradient
 let f:=voltInverse u a; refine ⟨f,?_⟩
 funext ⟨⟨x,k⟩,p⟩
 by_cases he:p=0; · subst p; exact (no_zero (x,k) f).trans (H.noHarm _).symm
 have hn:=ell_live he; have hv:=normK_ne n
 rcases x with ⟨_|i,_|_⟩
 · rw [row_c p k]; let z:=u (cBranch k,p)/(normK n*ℐ)
   have he(i:Axis): f (kBranch k i,-p)=amp p i * (kin p i*z):= by unfold f z; simp only [voltInverse,neg_neg]
   simp_rw [he,_root_.inv_mul_cancel_left₀ (Tone.nonz _ _), ← mul_assoc (kin p _) (kin p _) z, ← Finset.sum_mul, ell_sum]; unfold z; change _=u (cBranch k,p); field_simp [Complex.I_ne_zero]
 · exact (row_b p k f).trans (H.noB k p).symm
 · rw [row_A p k]; let g(j:Axis):= (amp p j)⁻¹ * f (vecBranch k j,-p)
   have hh(j:Axis): f (vecBranch k j,-p)=ell p/normK n * u (vecBranch k j,p):= by unfold f; simp only [vecBranch,Landau.gauge,voltInverse,neg_neg]
   have ht : (∑ j, kin p j* g j)=0:= by
      unfold g; simp_rw [hh]; let c:=ell p/normK n; 
      simp_rw [mul_left_comm ((amp p _)⁻¹) (ell p/normK n), mul_left_comm (kin p _) (ell p/normK n), ← Finset.mul_sum, H.vector,mul_zero]
   have hb : amp p i≠0:= nonz _ _
   rw [kn_vecProd p g, ht]; unfold g; rw [hh]; change _=u (vecBranch k i,p); simp only [mul_zero,sub_zero]; field_simp [hn,hv,hb]
 change _=u (kBranch k i,p); rw [row_K p k,ha]
 rw [show f (cBranch k,-p)= -ell p/normK n*a k p from (by unfold f; simp only [voltInverse,neg_neg]), show 1-Bloch.cell p (step i)= -(amp p i*(ℐ*kin p i)) from (by rw [← kn_diff,neg_sub])]
 field_simp

section abstract
-- quotient range: regular range intersect even-tensor data. independent of p slice.
variable {X:Type}[Fintype X]{p:Sector X}(K:Matrix X X ℂ)(e:Cog p)
def mirrorVec (e:Cog p)(x:X→ℂ) : X→ℂ := fun a=> e.spin (e.mode a)*x (e.mode a)
def mirrorT (e:Cog p)(x:X→ℂ) : X→ℂ := fun a=> e.spin a*x (e.mode a)
omit [Fintype X] in lemma sq_mirror (x:X→ℂ): mirrorVec e (mirrorVec e x)=x:=by funext a; unfold mirrorVec; rw [e.perm,←mul_assoc,mul_comm _ (e.spin a),e.holo,one_mul] -- inspect
lemma under_images (hp:e.phase K)(x:X→ℂ) : ((e.imageW K : Matrix X X ℂ) *ᵥ x)=mirrorVec e (K *ᵥ x):= by
 funext i; unfold mirrorVec Matrix.mulVec dotProduct; change (∑ j:X,e.imageW K i j*x j)=_; simp_rw [image_u hp]; rw [Finset.mul_sum]; apply sum_congr rfl; intro _ _; ring
lemma under_cols (x:X→ℂ): ((e.imageW K : Matrix X X ℂ) *ᵥ x)= K *ᵥ (mirrorT e x):= by
 funext i; unfold Matrix.mulVec dotProduct; refine Eq.trans ?_ (Equiv.sum_comp (Cog.axis e) (fun j=> K i j*mirrorT e x j)); apply sum_congr rfl; intro j _; change e.imageW K _ _ * x j= K i (e.mode j)* (e.spin (e.mode j)*x (e.mode (e.mode j))); rw [e.perm,imageW]; ring
lemma cascade_sum (x:X→ℂ): ( (e.Cascade K : Matrix X X ℂ) *ᵥ x)= K *ᵥ x + ((e.imageW K : Matrix X X ℂ) *ᵥ x):= by rw [← Matrix.add_mulVec]; rfl

lemma cascade_range (hp:e.phase K)(f:X→ℂ):
    (∃ u:X→ℂ, ((e.Cascade K : Matrix X X ℂ) *ᵥ u)=f)↔ (∃ u:X→ℂ, K *ᵥ u=f)∧ mirrorVec e f=f:=by
 constructor
 · rintro ⟨u,rfl⟩; rw [cascade_sum]; refine ⟨ ⟨u+mirrorT e u,by rw [Matrix.mulVec_add,under_cols]⟩, ?_⟩; rw [under_images _ e hp]; let g:= K *ᵥ u; rw [show mirrorVec e (g+mirrorVec e g)=mirrorVec e g+mirrorVec e (mirrorVec e g) from funext fun _=>mul_add ..,sq_mirror,add_comm]
 rintro ⟨⟨u,rfl⟩,he⟩; refine ⟨(1/2:ℂ) • u,?_⟩; rw [Matrix.mulVec_smul,cascade_sum,under_images _ e hp,he, smul_add, ← add_smul, show (1/2:ℂ)+1/2=1 from by norm_num,one_smul]
end abstract

lemma Quotient_range (u:A→ℂ):
    (∃ f, (QuotK G n) *ᵥ f=u)↔ OKFreq n u∧ mirrorVec (iota G n) u=u:=by
 change (∃ f, (((iota G n).Cascade M : Matrix A A ℂ) *ᵥ f)=u)↔_
 rw [cascade_range M (iota G n) (riverOK BankK.pin BankK.gov)]; refine and_congr_left fun _=>⟨ ?_,all_image ⟩; rintro ⟨v,hv⟩; rw [← hv]; exact ordinary_image v -- implicit binder order
end YM.FVAAlt2
