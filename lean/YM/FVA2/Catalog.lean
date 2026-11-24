import YM.FVA2.Terminal

/-!
# Finite comparison with a dictionary (mixing physical stencils)

No requirement that the coefficients in the mixing have limits, or are
bounded (or even real -- reality imposed when making physical choices). In
particular this accepts external Mat/labels at the exact native regulator; only
the order-filtration does some work, finite proof is BEFORE any estimates.
Resolving the mean sums into actual combos also covers sparse sets vs full label
ranges, no spurious sum over unused constituents.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2
open Function Set Filter Finset Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Book.Program MS.Puff.Engine MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian MS.Puff.Actors MS.Fleet
open PertExtension PertExtension.Orb Substitute Matrix Inversion Coupling Ends Inserted
open scoped Classical Topology ContDiff
namespace Catalog
variable {G:Gauge} {n:Side} {W: Type} [LinearOrder W]
set_option quotPrecheck false
local notation "A"=> Choice.allLetters G n
local notation "P"=> Words G n
local notation "I"=> FixedMode G n
local notation "M"=> Master G n true
local notation "π"=> σbranch (G:=G) (n:=n)
local infixr:70 " •𝕡 "=> multiple
local infixr:70 " ⋄ "=> (PermV π).core
local infixl:60 " ♠ "=> Trunk.core

-- hook for all actors below. `H`= geometric sites; Shift is anchor then relative.
variable {B : W→ Type}[∀ i,Fintype (B i)]
variable (a:Cover)(c:W→ Cover)(p:Team)(x:ℝ)(h: Even n.val)
local notation "μ"=> Marks (G:=G) (W:=W)
local notation "θ"=> NRG (Stripped p) x n G true
local notation "η"=> fun i:W=> a+c i
-- real-life program (unstretched by width factors including from spacing)
variable (V:(i:W)→ B i→ Unscaled G) (K:(i:W)→ B i→ℝ→Sc)

def pricing (p:Team) (V:(i:W)→ B i→ Unscaled G) (K:(i:W)→ B i→ℝ→Sc) (i : W) : Actor G := fun t=> ∑ F:B i,K i F t •𝕡 undilute (V i F) p t

-- product weights via scalar CPS
abbrev PCS (x : PowerSeries ℂ): Sc:= fun i=> PowerSeries.coeff i x
lemma pc_times (p q:PowerSeries ℂ): PCS (p*q) = PCS p ♠ PCS q:= by funext i; rw [PCS,PowerSeries.coeff_mul]; rfl
lemma to_one : PCS 1=Trunk.unit:= by funext i; rw [PCS,PowerSeries.coeff_one]; split_ifs with he; exact (if_pos he).symm; exact (if_neg he).symm

def multiplied (K:(i:W)→ B i→ℝ→Sc) (x:ℝ) (s: Finset W) (S:(i:s)→B i.val) := PCS (∏ i:s,PowerSeries.mk (K i.val (S i) x))
def receipt (p:Team) (x:ℝ) (a:Cover) (c:W→ Cover) (V:(i:W)→ B i→ Unscaled G) (K:(i:W)→ B i→ ℝ→ Sc) (n:Side)(s: Finset W) : Sc:=
     ∑ T:(i:s)→ B i.val, multiple (multiplied K x s T) (substitute (shift p x) (pureVia n s (fun i=> V i.val (T i)) (fun w=>a+c w)))

-- price extensions, including no label when extending outside finite invoiced part.
noncomputable def Unwritten (G:Gauge): Unscaled G:={
   degree:=0
   stencil:=0
   bottom:= fun _ _=>rfl
   stencilVal:=fun _=>0
   invariant:=fun _ _ _=>rfl
   chart := fun _=> contDiffAt_const
   usesStencil:=fun _=> by rw [map_zero]; exact (ink_zero _).symm }
def fillV (V:(i:W)→ B i→ Unscaled G)(s:Finset W)(S:(i:s)→B i.val)(i:W) := if h:i∈s then V i (S ⟨i,h⟩) else Unwritten G

def proofAct (s:Finset W)(S:(i:s)→ B i.val)(w:W):Actor G := undilute (fillV V s S w) p
lemma mark_even (z:W→ Unscaled G) (s: Finset W): EvenSeries π (Marks (fun i=> undilute (z i) p) x n a c s):= by
    by_cases hv:s.card=1
    · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp hv
      rw [mark_me]; change EvenSeries π (promote (Mark_T G n a (c i)) _)
      rw [show promote _ _= substitute (shift p x) (promote ξ[(χ G n)ᵀ*Fourier G n] (listPay (n:=n) (fun i=>a+c i) z i)) from ?_]; swap
      · rw [install]; exact Program.comm ..
      have ht:= (even_coeff _).mp (prim_even (fun i=>a+c i) z i (n:=n)); apply (even_coeff _).mpr; intro j
      rw [rules]; refine Pure.sum _ (fun k _=>?_); apply Pure.smul; let F:=listPay (n:=n) (fun i=>a+c i) z i k; rw [promised]; change Pure π false (ξ[(χ G n)ᵀ*Fourier G n] (region.symm F).val); rw [asShade]; exact p_ψ.pure (region.symm F) (ht k)
    rw [mark_off hv]; exact Submodule.zero_mem _

local notation "Γ0" => μ (pricing p V K) x n a c
local notation "μΓ"=> Font π Γ0
lemma tag_bill (j:W): Γ0 {j}= ∑ i:B j, multiple (K j i x) ( pointL ℕ (Mark_T G n a (c j)) (undilute (V j i) p x)) := by rw [mark_me]; unfold pricing; rw [map_sum]; exact Finset.sum_congr rfl fun _ _=> filter_r ..
lemma tag_even (u:Finset W) : EvenSeries π (Γ0 u):= by
   by_cases hv:u.card=1
   · obtain ⟨j,rfl⟩:= Finset.card_eq_one.mp hv; rw [tag_bill]; refine Submodule.sum_mem _ (fun i _=>?_)
     have ht:= mark_even (G:=G) (n:=n) a c p x (fun _=> V j i) {j}; rw [mark_me] at ht
     apply (even_coeff _).mpr; intro z; rw [waveRight]; refine Pure.sum _ (fun k hk=> Pure.smul _ ?_); exact (even_coeff _).mp ht _
   rw [mark_off hv]; exact Submodule.zero_mem _

-- Σ over assignments to subset. Equivalence splitting off each head.
variable {u:W}{s:Finset W}(h':u∉s)
private abbrev Assign (B:W→Type) (s:Finset W):= (i:s)→B i.val
private def absorb (h':u∉s) (i:B u × Assign B s) (w: ↥(insert u s)): B w.val:= by
    by_cases hw:w.val=u; exact hw.symm ▸ i.1
    exact i.2 ⟨w.val,mem_of_mem_insert_of_ne w.property hw⟩
private abbrev headD {u:W}{s:Finset W} : ↥(insert u s) := ⟨u,mem_insert_self ..⟩
private abbrev origD {u:W}{s:Finset W} (w:s) : ↥(insert u s) := ⟨w.val, mem_insert_of_mem w.property⟩
local notation "D"=> absorb h' (B:=B)
private lemma absorbed (t:B u × Assign B s)(w:s): D t (origD w)=t.2 w:= by unfold absorb; rw [dif_neg (show ¬(origD w (u:=u)).val=u from fun he => h' ((show _=_ from he) ▸ w.property))]
private lemma absorbed_first (t:B u × Assign B s): D t headD=t.1:= by unfold absorb; rw [dif_pos (show (headD (u:=u) (s:=s)).val=u from rfl)]
private def boxes (h':u∉s) : (B u× Assign B s) ≃ Assign B (insert u s):={
   toFun:= absorb h'
   invFun p:= (p headD,fun i=>p (origD i))
   left_inv x:= by apply Prod.ext; exact absorbed_first h' _; exact funext (absorbed h' _)
   right_inv T:= by
      funext i; by_cases hi:i.val=u
      · rw [show i=headD from Subtype.ext hi]; exact absorbed_first h' _
      let z:s:=⟨i.val,mem_of_mem_insert_of_ne i.property hi⟩; exact absorbed h' _ z }

private lemma bill_more (p : B u × Assign B s): multiplied K x (insert u s) (D p)= K u p.1 x ♠ multiplied K x s p.2 := by
    let f w:= if h:w∈insert u s then PowerSeries.mk ( K w ( D p ⟨w,h⟩ ) x ) else 0
    have ht (i: ↥(insert u s)): PowerSeries.mk (K i.val ( D p i ) x)=f i.val:= by simp only [f,dif_pos i.property]
    have hv : f u=PowerSeries.mk (K u p.1 x):= by change f (headD (u:=u) (s:=s)).val=_; rw [← ht, absorbed_first]
    unfold multiplied; simp_rw [ht]; rw [ Finset.prod_coe_sort,Finset.prod_insert h', hv,pc_times, ← Finset.prod_coe_sort];
    have hh : ∀ i:s,f i.val=PowerSeries.mk ( K i.val (p.2 i) x):=by intro i; change f (origD (u:=u) i).val=_; rw [← ht,absorbed]
    simp_rw [hh]; rw [show PCS (PowerSeries.mk (K u p.1 x)) =K u p.1 x from funext (fun i=> PowerSeries.coeff_mk ..)]
lemma markDepends {y z:W→Unscaled G}(s:Finset W) (h:∀ i∈s,y i=z i) : Font π (Marks (fun i=> undilute (y i) p) x n a c) s= Font π (Marks (fun i=> undilute (z i) p) x n a c) s := by
    induction s using Finset.induction_on with
    | empty=> rw [show Font π _ ∅ =(PermV π).unit from Puff.Stencil.simple_E _ _ _ (show Marks (fun i=>undilute (y i) p) x n a c ∅=0 from mark_off (by simp) ..), show Font π _ ∅ =(PermV π).unit from Puff.Stencil.simple_E _ _ _ (show Marks (fun i=>undilute (z i) p) x n a c ∅=0 from mark_off (by simp) ..) ]
    | insert u s hu IH=>
       rw [Font, Font, Puff.Stencil.cheers _ (mark_even _ _ _ _ y) (fun _ hu=> mark_off hu ..) s u hu,Puff.Stencil.cheers _ (mark_even _ _ _ _ z) (fun _ hu=> mark_off hu ..) s u hu,
           mark_me,mark_me,h u (Finset.mem_insert_self ..)]; exact congr_arg _ (IH fun i hi=> h i (mem_insert_of_mem hi))
lemma Font_bills (s:Finset W) : μΓ s= ∑ T: (i:s)→B i.val, multiplied K x s T •𝕡 ( Font π (μ (proofAct p V s T) x n a c) s) := by
    induction s using Finset.induction_on with
    | empty=>
       -- empty product terms
       have ht (y:W→Actor G): Font π ( Marks y x n a c ) ∅=(PermV π).unit := Puff.Stencil.simple_E _ _ _ (show Marks y x n a c ∅=0 from mark_off (by simp) ..)
       have he (p:(i : ↥(∅:Finset W)) → B i.val): multiplied K x ∅ p=Trunk.unit:= by unfold multiplied; rw [Fintype.prod_empty,to_one] -- inspect
       simp_rw [ht, he,multipleK]; simp
    | insert u s hu IH=>
       rw [Font, Puff.Stencil.cheers _ (tag_even a c p x V K) (fun _ hx=> mark_off hx ..) s u hu]; change _ ⋄ μΓ s=_; rw [ IH, tag_bill ];
       rw [ ← Equiv.sum_comp (boxes (B:=B) hu), Fintype.sum_prod_type ]; simp_rw [ map_sum, LinearMap.sum_apply];
       rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>?_))
       let D':= absorb hu (i,j); let y:= fillV V (insert u s) D';
       have hU : y u=V u i:= by
         unfold y fillV; rw [dif_pos (mem_insert_self ..), show D' _= i from absorbed_first hu (i,j)]
       have hf := Puff.Stencil.cheers (PermV π) (mark_even (G:=G) (n:=n) a c p x y) (fun _ hx=>mark_off hx ..) s u hu
       have he : ∀ v∈s, y v=fillV V s j v:= by
          intro v hv; unfold y fillV; rw [dif_pos hv,dif_pos (mem_insert_of_mem hv), show D' _=j (⟨v,hv⟩:s) from absorbed hu (i,j) ⟨v,hv⟩]
       change _ = ( multiplied K x (insert u s) D') •𝕡 Font π (Marks (fun i=> undilute (y i) p) x n a c) _
       rw [show multiplied K x (insert u s) D'=K u i x ♠ multiplied K x s j from bill_more x K hu _, show Font π _ (insert u s) = (Marks (fun i=>undilute (y i) p) x n a c {u}) ⋄ (Font π (Marks (fun i=>undilute (y i) p) x n a c) s) from hf, markDepends a c p x s he,mark_me,hU]
       rw [ act_l, act_q,repeatedS ]; rfl

include h
lemma blend (s: Finset W) : PhysicalSum G p x n true s c a (pricing p V K) (receipt p x a c V K n s) := by
    unfold PhysicalSum Endμ receipt
    rw [Font_bills]; simp_rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_
    let z:=fillV V s i; have ht:= dressed_vertices_together p x h c s z a; have hv:= buys (show Matrix I I ℂ from M) π (multiplied K x s i) ht
    have he : (fun j:s=> z j.val) = fun j:s=> V j.val (i j):= by funext j; unfold z fillV; rw [dif_pos j.property]
    rw [he] at hv; exact hv

end Catalog
end YM.FVA2
