import YM.FVA2.PlaneTime
/-!
# exact engineering scale obstruction

 Algebra of grade projections on Buffer. We will detect grade drops via polynomial log dilation,
 including which mass-independent adjustment uses the same object.
-/
set_option autoImplicit false
set_option maxHeartbeats 230000
noncomputable section
namespace YM.FVA2.Verne
open Function Filter Set Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Detector PositionX.Ribbon
open MS.Menus ColorCode
open scoped Topology ContDiff Classical
variable {G:Gauge} (F: Labels.Frames G) (d e j:ℕ)
def eng (φ:ℕ→ℝ) (d:ℕ):Module.End ℂ (E F d):= scalePolDiff F (fun a=>(φ a.1:ℂ)) d
-- arity.No limitation
variable {d e}
local notation "Γ"=> eng F
local notation "Fv"=> scalePolDiff F

variable (φ ψ:ℕ→ℝ)(i l k:BasisIx G d)
local notation "W"=>E F d
local notation "Ω"=>sameAxis F d
lemma massX : Γ φ d (Ω i) = ((φ i.size):ℂ) • Ω i := physical_inj F ( by rw [eng, scalePol_physical,map_smul ]; exact scalePol_pure F ( fun a=>(φ a.1:ℂ) ) (physicalLabel F d (Ω i)) ( graded F i ) (m:=(i.size,i.grade)) )
lemma coordφ (v:W): (Ω).coord i (Γ φ d v)= ( ( φ i.size ):ℂ ) * (Ω).coord i v := by
    rw [← (Ω).sum_repr v]; simp_rw [ map_sum,map_smul,massX,map_smul,Module.Basis.coord_apply,Module.Basis.repr_self_apply ]; rw [ Finset.mul_sum ]; refine Finset.sum_congr rfl fun k hk=>?_ ; by_cases hv:k=i <;> simp [hv,mul_comm]
lemma starφ (p:E F d) : (Model F).conj (hierarchy F).spin d (Γ φ d p)= Γ φ d ((Model F).conj (hierarchy F).spin _ p):= scalePol_star F _ _ (fun _=> Complex.conj_ofReal _) p
lemma ride (s: Ortho)(p:W): Γ φ d (Extra.FD.rideO F s d p)= Extra.FD.rideO F s d (Γ φ d p):=(scalePol_spin F (fun a=>(φ a.1:ℂ)) s p).symm
lemma riseφ (h:e≤d): Γ φ d ∘ₗ up F h = up F h ∘ₗ Γ φ e:= LinearMap.ext fun p=> Eq.symm (scalePol_up F _ h p)
lemma preserveφ (p:E F d)(h:p∈ lower F e d)(hv:e≤d): Γ φ d p∈ lower F e d:= by rw [up_pre _ hv] at h ⊢; obtain ⟨v,rfl⟩:=h; exact ⟨ Γ φ e v,scalePol_up F _ hv _ ⟩
lemma starUnit : Γ φ d ((Model F).unit d )= (φ 0 : ℂ ) • (Model F).unit d:= scalePol_unit F _
abbrev get (t:ℕ)(x:ℕ) : ℝ:= if t=x then 1 else 0
def block : Module.End ℂ (E F d):= eng F (get j) d -- implicit d, . etc.
local notation "∂" r=> block (d:=d) F r
lemma work (v:E F d): ∑ k∈Finset.range (d+1),block F k (d:=d) v=v:= by
    have he : ∑ k∈Finset.range (d+1),block F k (d:=d)=1:= by
        apply (Ω).ext; intro i; rw [ LinearMap.sum_apply ]; unfold block; simp_rw [ massX ]; rw [← Finset.sum_smul, ←Complex.ofReal_sum ]; have he: ∑ k∈Finset.range (d+1), get k i.size=1:= (by simp [get, Finset.mem_range, i.1.isLt, Glyph.size]); rw [he]; simp
    rw [ ← LinearMap.sum_apply, he ]; rfl
local notation "B"=>Pert.Position.Buffer F d
lemma unit_lowerφ (p:Pert.Position.Buffer F d)(v:E F d) (h:v∈ lower F e d)(ht:e≤d) : (bufferL F p) v∈ lower F e d:= by
    rcases lt_or_eq_of_le ht with hv|rfl; exact p.property.2.1 e hv v h; rw [up_pre _ le_rfl ]; exact ⟨_,show up F le_rfl (bufferL F p v)=(bufferL F p) v from by rw [up_same]; rfl⟩
-- produce linear projection on increments not requiring invertibility. rotations survive.
def pairφ (p:Pert.Position.Buffer F d): Pert.Position.Buffer F d:=
    let z:= Γ φ d ∘ₗ bufferL F p ∘ₗ Γ ψ d; ⟨ (z.restrictScalars ℝ).toContinuousLinearMap, by
    refine ⟨?_,fun k hk v hv=> ?_,fun v=> ?_,fun s v=>?_,map_smul z _⟩
    · change z _= 0; unfold z; rw [LinearMap.comp_apply,LinearMap.comp_apply,starUnit, map_smul, show bufferL F p _= 0 from p.property.1, smul_zero, map_zero]
    · change z v∈_; unfold z; simp only [LinearMap.comp_apply]; exact preserveφ F φ (bufferL F p (Γ ψ d v)) ( unit_lowerφ F p ( Γ ψ d v ) (preserveφ F ψ v hv hk.le) hk.le ) hk.le
    · have he(v): (Model F).conj (hierarchy F).spin d ( bufferL F p v )= bufferL F p ((Model F).conj (hierarchy F).spin d v):= p.property.2.2.1 v; change (Model F).conj _ _ ( z v )= z _; unfold z; rw [LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.comp_apply,starφ,he,starφ]
    change Extra.FD.rideO F s.ortho _ ( z v )=z _; unfold z; simp_rw [LinearMap.comp_apply,← ride, bufferL_eq,p.property.2.2.2.1 ,← ride] ⟩
lemma pairs (p:Pert.Position.Buffer F d)(v:W): (pairφ F φ ψ p).1 v=Γ φ d (bufferL F p (Γ ψ d v)):= rfl
def Down : Module.End ℝ (Pert.Position.Buffer F d) where
   toFun p:= pairφ F φ ψ p
   map_add' a b:= by ext1; ext1 v; rw [pairs ]; change Γ φ d (_+_) = Γ φ d _+ Γ φ d _; rw [map_add]; rfl
   map_smul' r p:= by ext1; ext1 v; rw [pairs ]; change Γ φ d (r • _) = r • Γ φ d _; rw [LinearMap.map_smul_of_tower]; rfl
def withinBlock : Module.End ℝ (Pert.Position.Buffer F d):= ∑ k∈ Finset.range (d+1), Down (d:=d) F (get k) (get k)
lemma reprφ (p:Pert.Position.Buffer F d): (Ω).coord k (bufferL F ( Down F φ ψ p ) (Ω i))= (( φ k.size : ℂ ) * ( ψ i.size : ℂ )) * (Ω).coord k (bufferL F p (Ω i)):= by
    change (Ω).coord k (Γ φ d (bufferL F p (Γ ψ d (Ω i))))=_; rw [coordφ, massX,map_smul, map_smul, smul_eq_mul, mul_assoc ]
lemma coordDown (p:Pert.Position.Buffer F d): (Ω).coord k (bufferL F (withinBlock F p) (Ω i)) = if k.size=i.size then (Ω).coord k ( bufferL F p (Ω i)) else 0:= by
    let L(x:Pert.Position.Buffer F d):= (Ω).coord k (bufferL F x (Ω i))
    -- easier `Finset`, Subtype.val. bufferL_eq
    rw [withinBlock, LinearMap.sum_apply ]; simp_rw [bufferL_eq,AddSubmonoidClass.coe_finsetSum, sum_apply,map_sum]; simp_rw [ ← bufferL_eq, reprφ ]; split
    next H => rw [H]; rw [Finset.sum_eq_single i.size]; simp [get]; intro j hj hv; simp [get,hv]; intro h; exfalso; exact h (Finset.mem_range.mpr i.1.isLt)
    next H => apply Finset.sum_eq_zero; intro j hj; unfold get; split <;> split <;> simp_all
-- triangular law needed of buffer itself, not only scaling committed.
lemma beacon_lower {i:BasisIx G d}{k:ℕ}(h: i.size ≤ k)(hv:k≤ d) : Ω i∈ lower F k d := by
   let j:BasisIx G i.size:= MS.Land.read ( d:=i.size ) i.2; let p:= sameAxis F _ j; rw [up_pre F hv]; exact ⟨ up F h p,( up_mul F h hv p ).trans (same_up F (h.trans hv) j) ⟩
lemma trim0 (p:E F e)(h:e≤d) : trim F e d (up F h p)=up F h p:= by unfold trim; rw [ ← scalePol_up ]; exact congr_arg ( up F h ) ( trim_self F le_rfl _ )
lemma nil_coord {i:BasisIx G d} (p:E F d) (hp:p∈lower F e d)(he:e < i.size): (Ω).coord i p=0:= by
   have hh : e≤d:= he.le.trans (not_under i); rw [up_pre F hh] at hp; obtain ⟨p,rfl⟩:=hp; let f(k:ℕ):ℝ:= if k≤e then 1 else 0; have hf: trim F e d= Γ f d:= congr_arg (fun f=>Fv f d) ( funext fun i=>( by unfold prune f; split <;> simp ) ); rw [← trim0 F p hh, hf,coordφ ]; simp [f, not_le_of_gt he]
lemma triangular0 (p: Pert.Position.Buffer F d) (h:l.size < i.size) : (Ω).coord i (bufferL F p (Ω l))=0:= nil_coord F _ (unit_lowerφ F p _ (beacon_lower F le_rfl (not_under l)) (not_under l)) h
-- diagonal-block preserves convolution.
lemma hom (a b:Pert.Position.Buffer F d) : withinBlock F (Ribbon.followB a b)=Ribbon.followB (withinBlock F a) (withinBlock F b):= by
    apply Ribbon.follows_right; apply (Ω).ext; intro i; apply (Ω).repr.injective; ext k; change (Ω).coord k (bufferL F _ (Ω i))=(Ω).coord k (bufferL F _ (Ω i)); rw [ coordDown ];
    let C (a b:Pert.Position.Buffer F d) (j:BasisIx G d):= (Ω).coord j (bufferL F b ( Ω i ))* (Ω).coord k (bufferL F a ( Ω j ));
    have he(a b:B): (Ω).coord k (bufferL F (Ribbon.followB a b) (Ω i))=∑ j,C a b j:= by
        rw [ Ribbon.follow_buff,LinearMap.comp_apply ]; nth_rw 1 [← (Ω).sum_repr (bufferL F b ( Ω i)) ]; simp_rw [ map_sum,map_smul]; rfl
    rw [ he, he ]; split
    next h=> refine Finset.sum_congr rfl fun j _=>?_ ; unfold C; rw [coordDown,coordDown ]; by_cases ha:j.size=i.size; · rw [if_pos ha,if_pos (h.trans ha.symm)];
             have ht:k.size≠j.size:= fun g=> ha ( g.symm.trans h ); rcases lt_or_gt_of_ne ha with hm|hm; · rw [triangular0 F k j a ( h.symm ▸ hm )]; simp only [ha, ↓reduceIte, zero_mul, mul_zero];
             rw [triangular0 F j i b hm]; simp only [ha, ↓reduceIte,zero_mul]
    next h=> symm; refine Finset.sum_eq_zero fun j _=> ?_ ; unfold C; rw [coordDown,coordDown]; by_cases ht:j.size=i.size; · rw [if_neg (show k.size≠ j.size from fun hv=> h (hv.trans ht)),mul_zero]
             rw [if_neg ht,zero_mul]
lemma diagonal (p:Pert.Position.Buffer F d): withinBlock F (withinBlock F p)= withinBlock F p:= by
    apply follows_right; apply (Ω).ext; intro i; apply (Ω).repr.injective; ext k; change (Ω).coord k (bufferL F _ (Ω i))=(Ω).coord k (bufferL F _ (Ω i)); rw [coordDown,coordDown]; split <;> try simp [*]
lemma recognized (p:Pert.Position.Buffer F d) : withinBlock F p=p ↔ ∀ i k:BasisIx G d,i.size≠k.size→ (Ω).coord k (bufferL F p (Ω i))=0:= by
    constructor; · intro hp i k h; rw [ ← hp, coordDown, if_neg (Ne.symm h) ]
    intro hp; apply follows_right; apply (Ω).ext; intro i; apply (Ω).repr.injective; ext k; change (Ω).coord k (bufferL F _ (Ω i))=(Ω).coord k (bufferL F _ (Ω i)); rw [coordDown]; split; rfl; exact Eq.symm ( hp _ _ (Ne.symm (by assumption)) )
lemma diagStrict (p:Pert.Position.Buffer F d) : withinBlock F p=0 ↔ ∀ i k:BasisIx G d,i.size=k.size→ (Ω).coord k (bufferL F p (Ω i))=0 := by
    constructor
    · intro he i k h; have ht:= coordDown F i k p; rw [if_pos h.symm, he] at ht; rw [ ← ht ]; change (Ω).coord k 0=_; rw [map_zero]
    intro hp; apply follows_right; apply (Ω).ext; intro i; apply (Ω).repr.injective; ext k; change (Ω).coord k (bufferL F _ (Ω i))=(Ω).coord k 0; rw [coordDown, map_zero]; split; exact hp _ _ (Eq.symm ‹_›); rfl
lemma zoomBlock (p:B)(h:e≤d) : zoomL F h (withinBlock F p)= withinBlock F (zoomL F h p) := by
    have hu(k:ℕ)(p:B) : zoomL F h (Down F (get k) (get k) p)=Down F (get k) (get k) (zoomL F h p):= by
       apply follows_right; apply ( sameAxis F e ).ext; intro i; apply up_inj F h; let K(t):= eng F (get k) t;
       rw [bufferL_eq,zoomL_eq ]; change K d (bufferL F p (K d ( up F h ( sameAxis F e i ) )))=up F h ( K e ( bufferL F (zoomL F h p) ( K e ( sameAxis F e i ) ) ) ); have hx(v):K d ( up F h v )=up F h (K e v):= LinearMap.congr_fun ( riseφ F (get k) h ) v; simp_rw [ hx, bufferL_eq, ← zoomL_eq,hx ];
    unfold withinBlock; rw [ LinearMap.sum_apply,LinearMap.sum_apply,map_sum ]; simp_rw [hu]; symm; apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_; -- direction
    intro x hx hv; let K:= Down F (get x) (get x) (zoomL F h p); apply follows_right; apply (sameAxis F e).ext; intro i; apply (sameAxis F e).repr.injective; ext j; change (sameAxis F e).coord j (bufferL F K (sameAxis F e i))=(sameAxis F e).coord j (bufferL F (0:Pert.Position.Buffer F e) (sameAxis F e i)); rw [show bufferL F (0:Pert.Position.Buffer F e) (sameAxis F e i)=0 from rfl,map_zero]; obtain ht:= not_under i; simp_rw [K, reprφ, show get x i.size=0 from if_neg (show x≠ i.size from by simp_all;omega)]; simp
end YM.FVA2.Verne
