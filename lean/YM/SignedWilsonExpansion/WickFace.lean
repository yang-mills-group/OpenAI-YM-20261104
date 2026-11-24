import YM.SignedWilsonExpansion.PairFlow
import YM.FVA2.Scale.Functions
namespace YM.SignedWilsonExpansion.WickFace
/-! # Evaluation on the prescribed axial test, orientation `x-y`. Energy plane
    spatial axes 1,2 (using ordered axes `(1,2,0,3)` in the plane test convention).
    Auxiliary low horizon, padding units, linear-map cancellations. -/
noncomputable section
set_option autoImplicit false
open Function Filter Set MeasureTheory Finset
open Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Scale Scale.Level
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge} {n:ℕ}
abbrev Idx:=Normalize.Index
abbrev lantern (i:Idx):=cell (Normalize.left i) (Normalize.right i)
-- test e marker
local notation "i₀" => (3:Idx)
lemma lantern3: lantern i₀=cell 1 2:= rfl
abbrev wmark (G:Gauge)(i j:Idx):= team G (lantern i) (lantern j)
abbrev glow (G:Gauge)(i j:Idx): Sec G 4:= ⟨ wmark G i j, team_label _ _ le_rfl ⟩
abbrev lens (G:Gauge):= glow G i₀ i₀
lemma blaze : (lens G).val=Energy.raw G 1 2:=rfl
local notation "λ'" => glow G
local notation "M" => WickPol G
local notation "L" => Sec G 4
local notation "m" => Fintype.card G.ColorIndex
local notation "δ" => wmark G
lemma pure (i j:Idx) : proj (d:=4) 4 (glow G i j)= glow G i j:= by
    have hz(p q:Flavor 0): MvPolynomial.IsWeightedHomogeneous scaleW (team G p q) (4:ℕ):=by unfold team; apply MvPolynomial.IsWeightedHomogeneous.sum; exact fun i _=> ( symbol_hom (flavor (G:=G) 0 i p) (fun j=>j+2)).mul ( symbol_hom (flavor (G:=G) 0 i q) (fun j=>j+2))
    exact Level.same (G:=G) (j:=4) (by decide) (⟨_,(glow G i j).property,hz (lantern i) (lantern j)⟩:On.Grade G 4)
lemma money (t:ℝ)(i j:Idx): Level.Dial 4 t (glow G i j)= Extent.token t 4 • glow G i j:= by nth_rw 1 [← pure i j]; rw [Level.taken, pure]; rfl
lemma unit_dial (t:ℝ): Level.Dial 4 t (leaf G 4)= leaf G 4:= by nth_rw 1 [← Level.leaf_0]; rw [Level.taken, Level.leaf_0]; exact one_smul ℂ _ -- maybe unfold
lemma even4 (h:G.Simple)(p:L): Normalize.hinge 4 p=p:= Subtype.ext ( AxesTangent.same_low h p.val p.property )
-- Span on S for testing linear functionals
lemma at_low {V:Type}[AddCommMonoid V][Module ℂ V](h:G.Simple)(f g:L→ₗ[ℂ]V)(he:f ( Normalize.leaf G 4)=g (leaf G 4))(ht:∀ i j:Idx,f (glow G i j)=g (glow G i j))(p:L): f p=g p:= by
    let W:= Normalize.project 4 (G:=G); let Y:=LinearMap.eqLocus ( f.comp W ) ( g.comp W ); have hv (p:WickPol G)(H:p∈ shellSector G 4) : p∈Y := (Normalize.low_span Y h).2 ⟨ (by rw [LinearMap.mem_eqLocus]; rw [LinearMap.comp_apply, LinearMap.comp_apply]; rw [ show W (1:WickPol G)= leaf G 4 from seated (leaf G 4) ]; exact he ), fun i j _=> show Normalize.label G i j∈Y from (by rw [LinearMap.mem_eqLocus,LinearMap.comp_apply,LinearMap.comp_apply, show W _=glow G i j from ?_ ]; exact ht ..; exact seated (glow G i j)) ⟩ H
    have hh:= hv p.val p.property; change f (W p.val)=g (W p.val) at hh; rwa [show W p.val=p from seated p] at hh
-- faces. Introduced uniformly for later calling into geometry.
abbrev I (n:ℕ):= Fin n
variable (x:Stage n)
local notation "Ω" => moment G x.val
local notation "U" => (fun (_:Fin n)=> (1:WickPol G))
abbrev oneOnly (i:Fin n): M→ₗ[ℂ]ℂ:= (moment G x.val).toLinearMap (fun (_:Fin n)=>1) i
abbrev dyad (i j:Fin n) (b:M): M→ₗ[ℂ]ℂ:= (moment G x.val).toLinearMap (update (fun (_:Fin n)=>1) j b) i
abbrev journey (i j k:Fin n)(b c:M): M→ₗ[ℂ]ℂ:= (moment G x.val).toLinearMap (update (update (fun (_:Fin n)=>1) k c) j b) i
-- using carrier labels.Real scale via MPL. j first before k allowed by h.
variable (p q r:WickPol G)(i j k:Fin n)(hij:i≠j)(hjk:j≠k)(hik:i≠k)
include hij
lemma mate : dyad x i j p q= dyad x j i q p:= by unfold dyad; simp only [MultilinearMap.toLinearMap_apply]; rw [ Function.update_comm hij ]
lemma front : journey x i j k p q r=journey x j i k r q p:= by unfold journey; simp only [MultilinearMap.toLinearMap_apply]; rw [ update_comm hij ] -- check updating outer i
lemma dropI : dyad x i j p 1=oneOnly x j p:= by rw [ mate x _ _ i j hij ]; unfold oneOnly dyad; rw [ show update U i (1:WickPol G)=U from update_eq_self .. ]
omit hij
lemma coinS : oneOnly x (G:=G) i 1=1:= by unfold oneOnly; rw [ MultilinearMap.toLinearMap_apply,show update U i (1:WickPol G)=U from update_eq_self .. ]; exact Wick.constants x.val
include hjk
lemma rear : journey x i j k p q r=journey x i k j q p r:= by unfold journey; rw [ update_comm hjk ]
omit hjk
include hij hik
lemma dropJ : journey x i j k (G:=G) p q 1=dyad x j k q p:= by
   rw [front x p q _ _ _ _ hij]; unfold journey dyad; rw [ show update (update U k q) i 1=update U k q from ?_ ]
                                                                      -- value fit
   conv_lhs => rhs; rw [ ← show update U k q i=(1:WickPol G) from by simp [hik] ]
   exact update_eq_self ..
omit hij hik
section spots
abbrev bin (u:Idx)(c:G.ColorIndex): Factor G:= ⟨0,flavor (G:=G) 0 c (lantern u)⟩
abbrev ψ (a b:Factor G):= letter a * letter b
private lemma stock (u v:Idx) : wmark G u v=∑ a:G.ColorIndex,ψ (bin u a) (bin v a):=rfl
variable (a b u w:Factor G)
local notation "Y" => (x.val.ofLp)
local notation "P" => (Fin n × Factor G)
lemma wink_m : oneOnly x i (ψ a b)=0 := by
    let Q':List P:= [(i,a),(i,b)]; rw [oneOnly, MultilinearMap.toLinearMap_apply, show update U i (ψ a b)=bag Prod.fst Prod.snd Q' from (by funext j; by_cases H:j=i <;> simp [Q',bag,H,ψ] ) ]; rw [ bag_rec _ _ _ x.property ]; change pairCost linkEntry [(Y i, a), (Y i, b)]=_; rw [ pair_step,pulls_cons,link_zero,pulls_nil ]; simp
lemma single_off (a b:Idx): oneOnly x i (wmark G a b)=0:= by rw [stock, map_sum ]; simp_rw [wink_m, Finset.sum_const_zero ]
include hij
lemma price_pair : dyad x i j (ψ u u) (ψ a b) =2* linkEntry (Y i,a) (Y j,u)*linkEntry (Y i,b) (Y j,u):= by
    let Q':List P:= [(i,a),(i,b),(j,u),(j,u)]; unfold dyad; simp only [MultilinearMap.toLinearMap_apply ]; rw [ show update ( update U j (ψ u u) ) i (ψ a b)=bag Prod.fst Prod.snd Q' from ?_, bag_rec _ _ _ x.property ]; swap; · funext l; by_cases he:l=i; subst l; simp [Q',bag,ψ, hij]; by_cases H:l=j; subst l; simp [Q',bag,ψ,hij.symm]; simp [Q',bag,he,H]
    change pairCost linkEntry [(Y i,a),(Y i,b),(Y j,u),(Y j,u)]=_; simp only [pair_step,pulls_cons,link_zero,pulls_nil ]; rw [pairCost]; ring
include hik hjk
lemma price_trip : journey x i j k (ψ u u) (ψ w w) (ψ a b) = 4*( linkEntry (Y i,a) (Y j,u)*linkEntry (Y i,b) (Y k,w)+linkEntry (Y i,a) (Y k,w)*linkEntry (Y i,b) (Y j,u) )* linkEntry (Y j,u) (Y k,w):= by
    let Q':List P:= [(i,a),(i,b),(j,u),(j,u),(k,w),(k,w)]; unfold journey; simp only [MultilinearMap.toLinearMap_apply]; rw [ show update (update (update U k (ψ w w)) j (ψ u u)) i (ψ a b)=bag Prod.fst Prod.snd Q' from ?_,bag_rec _ _ _ x.property ]; swap;
    · funext l; by_cases he:l=i; · subst l; simp [Q',bag,ψ,hij,hik]
      by_cases hx:l=j; subst l; simp [Q',bag,ψ,hij.symm,hjk]; by_cases hu:l=k; subst l; simp [Q',bag,hik.symm,hjk.symm,ψ]; simp [bag,Q',he,hx,hu]
    change pairCost linkEntry [(Y i,a),(Y i,b),(Y j,u),(Y j,u),(Y k,w),(Y k,w)]=_; simp only [pair_step,pulls_cons,pulls_nil,link_zero, mul_zero, zero_mul,add_zero,zero_add ]; rw [pairCost]; ring
end spots
/-! magnetic label. Geometry channel.Channels formula. -/
def Holds := ∀ i:Fin n,∃ v:ℝ,x.val i=v • basis 3
abbrev timeLine (t:ℝ):E4:= t • basis 3
variable (hx:Holds x)
include hx
lemma gap (i j:Fin n) : ∃ v:ℝ,x.val i-x.val j=timeLine v:= by obtain ⟨a,ha⟩:= hx i; obtain ⟨b,hb⟩:= hx j; exact ⟨a-b,by rw [ha,hb]; exact (sub_smul ..).symm⟩
private lemma beam3 (q:E4)(t:ℝ): ‖timeLine t‖=|t|:= by simp [timeLine,norm_smul]
local notation "K" => (fun x:E4=>4* Maxwell.normal*(‖x‖^2)⁻¹^2)
def pay (x:Stage n)(i j:Fin n):ℝ:=4* Maxwell.normal* (‖x.val i-x.val j‖^2)⁻¹^2
def bitT (a:Idx):ℝ:= if a = i₀ then 1 else 0
omit hx hij hik hjk -- inclusion status price_trip include/hjk persists? end section resets to just ~
lemma pay_m (i j:Fin n): pay x i j= pay x j i:= by unfold pay; rw [norm_sub_rev (x.val i)] -- correct
include hij
lemma positive : 0<pay x i j:= by unfold pay; have ht:0<‖x.val i-x.val j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr ( ( show Injective x.val.ofLp from x.property ).ne hij )); have hp:= Maxwell.normal_pos; positivity
include hx
lemma fare_line (a b:G.ColorIndex) (u:Idx) :
    linkEntry ( x.val i, bin u a ) ( x.val j, bin i₀ b )= if a=b then (( ( bitT u*pay x i j):ℝ):ℂ) else 0:= by
    rw [ link_eq _ _ _ _ (( show Injective x.val.ofLp from x.property ).ne hij) ]; obtain ⟨t,h⟩:= gap x hx i j; rw [ show Free.K (bin u a).snd (bin i₀ b).snd _ _ = _ from (show Free.K (bin u a).snd (bin i₀ b).snd (x.val i) (x.val j)= (if a=b then bareCurl (Normalize.left u) (Normalize.right u) 1 2 (x.val i-x.val j) else 0) from omega_K_eq _ _ _ _ _ _ (( show Injective x.val.ofLp from x.property ).ne hij) ) ]; split_ifs with H; swap; exact Complex.ofReal_zero
    rw [ bare_formula _ _ _ _ (sub_ne_zero.mpr ( ( show Injective x.val.ofLp from x.property ).ne hij)) ]; apply congr_arg; unfold pay; rw [h]; unfold wedge; simp [house, houseM, kr_eq, timeLine]; fin_cases u <;> simp [Normalize.left,Normalize.right,bitT]
-- payoff multiplicity
lemma dy_bill (a b:Idx): dyad x i j (wmark G i₀ i₀) (wmark G a b)=
                        (( (bitT a*bitT b)*(m*2*pay x i j^2):ℝ):ℂ ):= by
   rw [ stock a b, map_sum ]; -- stock argument order
   have he(a b:Factor G): dyad x i j (wmark G i₀ i₀) (ψ a b)= ∑ u:G.ColorIndex, dyad x i j (ψ (bin i₀ u) (bin i₀ u)) (ψ a b):= by
       rw [ mate x _ _ _ _ hij, stock,map_sum ]; exact Finset.sum_congr rfl fun i _=> mate x _ _ _ _ hij.symm
   simp_rw [ he, price_pair x i j hij, fare_line x i j hij hx ]; simp only [ mul_ite, ite_mul, mul_zero, zero_mul ]; simp [bitT,sq]; split_ifs <;> push_cast <;> ring
include hik hjk
lemma tri_bill (a b:Idx): journey x i j k (wmark G i₀ i₀) (wmark G i₀ i₀) (wmark G a b) = (( (bitT a*bitT b)*(m*8*pay x i j*pay x i k*pay x j k):ℝ):ℂ):= by
    rw [stock a b,map_sum]; have he(a b:Factor G) (j k:Fin n)(S:M)(hx:i≠j): journey x i j k (wmark G i₀ i₀) S (ψ a b)=∑ u:G.ColorIndex, journey x i j k (ψ (bin i₀ u) (bin i₀ u)) S (ψ a b):= by
       rw [ front x _ _ _ _ _ _ hx,stock,map_sum ]; exact Finset.sum_congr rfl fun _ _=> front x _ _ _ _ _ _ hx.symm
    have hq(a b:Factor G)(S:M):journey x i j k S (wmark G i₀ i₀) (ψ a b)=∑ u:G.ColorIndex, journey x i j k S (ψ (bin i₀ u) (bin i₀ u)) (ψ a b):= by
       rw [ rear x _ _ _ _ _ _ hjk, he _ _ k _ _ hik ]; exact Finset.sum_congr rfl fun _ _=> rear x _ _ _ _ _ _ hjk.symm
    have hu (c:G.ColorIndex): (∑ u:G.ColorIndex, ∑ w:G.ColorIndex, journey x i j k (ψ (bin i₀ u) (bin i₀ u)) (ψ (bin i₀ w) (bin i₀ w)) (ψ (bin a c) (bin b c)))= ( bitT a*bitT b:ℂ )*((8*pay x i j*pay x i k*pay x j k:ℝ):ℂ):= by
       simp_rw [ price_trip x i j k hij hjk hik, fare_line x i j hij hx,fare_line x i k hik hx,fare_line x j k hjk hx ]; -- finish sums
       rw [ Finset.sum_eq_single_of_mem c (mem_univ _) ]; swap; · intro b _ h; simp [Ne.symm h]
       rw [ Finset.sum_eq_single_of_mem c (mem_univ _ ) ]; swap; · intro b _ h; simp [Ne.symm h]
       simp only [bitT, ↓reduceIte]; push_cast; ring
    simp_rw [he _ _ _ _ _ hij,hq, hu, Finset.sum_const]; simp; push_cast; ring
omit hx hij hik hjk
lemma norm_value (i j:Fin n)(h:i≠j) : pay x i j=(Real.pi^2*‖x.val i-x.val j‖^4)⁻¹:= by unfold pay Maxwell.normal; field_simp [show Real.pi≠0 from Real.pi_ne_zero];
end
end YM.SignedWilsonExpansion.WickFace
