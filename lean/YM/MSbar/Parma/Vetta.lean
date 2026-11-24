import YM.MSbar.Parma.Indus
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}(g:Ratio c n)(P:Cross g.count (TypeFace 1) (TypeFace 1))
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "ℓ"=>Measuring.chart n G
local notation "T"=>Measuring.chart c G
local notation "L"=>(g.count.val:ℝ)
local notation "R'"=>installed g P
open MvPolynomial Cane
variable (f:Nesting G n)(F:ℝ → Wilson.Config G n→ℝ)(R:PathData G)(l:Clip)(v:G.ColorIndex){a η B C b H Z D w A:ℝ}{r m p k N:ℕ}
variable (hG:G.Simple)(hf:Trend F f R l p)(hK: Keeps f p (sun G v)) (hr:r≤p)(hx:0<r)(hb:0≤b)(hη:6≤N)
local notation "T₀"=>teethT f r
local notation "F₁"=>clue (teethT f r)
variable (hZ:Tin (Measuring.chart n G) b N (r+1) w (teethT f r) Z) (hw:1≤ w) (he:∀ i<r, Tokew (Measuring.chart n G) b N 3 0 (PowerSeries.coeff i (tariff n p l R f)) A)
local notation "d"=> (4*100^3/(n.val:ℝ)^3)
variable (h:Cane P D η a H k N) (hp:3≤k) (hg:2≤g.count.val)(hT:a/(g.count.val:ℝ) ≤ b) (ha:0≤ A)
local notation "ν"=>Cane.value a D η H N k
local notation "E"=> crownB G H η D k
local notation "M"=>Rolling.rail (maple R' G) T₀
-- costs pre: function of η strip etc.C includes.D.Stack Hyper origin.Genuine L gain. output sum.
noncomputable def precP (i m:ℕ) (V H:ℝ):= (V)^(m+1)
noncomputable def highP (m:ℕ)(a D η H:ℝ)(N k:ℕ):=(Cane.value a D η H N k)^(m+1)
noncomputable def lowP (G:Gauge)(m:ℕ)(a D η H:ℝ)(N k:ℕ):=
    (Cane.value a D η H N k)*(2*(feed a η H D N k m)*4^(4-m) + (crownB G H η D k)^m*(4*100^3*(64*100)))
noncomputable def fixP (G:Gauge)(r:ℕ) (a D η H:ℝ)(N k:ℕ):= (∑ i∈Finset.Icc 1 3, lowP G i a D η H N k) + ∑ i∈ Finset.Icc 4 (r+1), highP i a D η H N k
noncomputable def aid (G:Gauge)(h:Side)(m r:ℕ)(a D η H:ℝ)(N k:ℕ):= (h.val:ℝ)^3*(Cane.value a D η H N k)*(crownB G H η D k/(h.val:ℝ))^m * Lis.statue G r (m-1)
noncomputable def fixedG (G:Gauge)(h:Side)(r:ℕ)(a D η H:ℝ)(N k:ℕ) := ∑ i∈Finset.Icc 1 3,aid G h i r a D η H N k
local notation "C'"=> fixP G r a D η H N k
local notation "s'"=> fixedG G g.count r a D η H N k
include h
lemma valueG (t:ℕ) (X':Side):0 ≤ Cane.value a D η H N k ∧0 ≤ feed a η H D N k t ∧ 0 ≤ crownB G H η D k ∧ 0 ≤ fixP G t a D η H N k∧∀ r:ℕ,0≤ fixedG G X' r a D η H N k:=by
   have hH:0 ≤ H:= zero_le_one.trans h.E0; have hx:=h.D0; have hv:=Cane.specs P h; have hp(i):0≤feed a η H D N k i:=by unfold feed; positivity
   have he:0 ≤ crownB G H η D k:=by unfold crownB; positivity
   refine ⟨hv,hp t,he,add_nonneg (Finset.sum_nonneg fun i _=>?_) (Finset.sum_nonneg fun i _=>?_),fun r=>Finset.sum_nonneg (fun i _=>?_)⟩
   · unfold lowP; have :=hp i; positivity
   · exact pow_nonneg hv _
   unfold aid; have ht:=Lis.statue_pos G r (i-1); positivity
include hG hf hK hr hx hp he ha hw hg hZ hT hb hη
lemma currency (m:ℕ)(hi:m≤ r+1)(hh:m∈ Set.Icc 1 3)(x:Y): cog T a N M m x ≤ (C'/L*Z+s'*(w^4*A))/w^(m+1):=by
    have hw':0< w:=zero_lt_one.trans_le hw
    let U₀:= Z/w^(m+1); let c':=4*100^3*(64*100:ℝ); have hc:0≤c':=by unfold c';norm_num
    let v':= slopeY n m U₀; have ht:= Lis.statue_pos G r (m-1); have hZ':=hZ.dec
    obtain ⟨h₁,h₂⟩:= hh
    have hU:0≤ U₀:=by unfold U₀; positivity
    have hx': v' ≤ (Z / w^(m+1))*(c'/L^3):=by
        unfold v' slopeY; apply mul_le_mul_of_nonneg_left _ hU
        let N':ℝ:= n.val
        have hk : L ≤ N':=by unfold N'; exact_mod_cast (show g.count.val ≤ n.val from by have hx : n.val = c.val*g.count.val:= g.exact_size; rw [hx,mul_comm]; exact Nat.le_mul_of_pos_right _ c.property)
        apply le_trans (b:=4*100^3/N'^3*(64*100:ℝ)) _ (le_trans (b:= c'/N'^3) _ _)
        · exact mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) (by positivity)
        · exact le_of_eq (by unfold c';ring)
        apply div_le_div_of_nonneg_left hc (by positivity); gcongr
    have hz:0≤v':=by unfold v' slopeY; split <;> positivity
    apply le_trans (price₁ g P f F R l v hG hf hK hr hx hb hη hZ hw' he h hp hg hT ha m hi ⟨h₁,h₂⟩ _ (show 0 ≤ v'+ _ from add_nonneg hz (mul_nonneg ht ha)) (fun j=>ropes g P f F R l v hG hf hK hr hx hb hη hZ hw' he h hp hg hT ha _ hi ⟨h₁,h₂⟩ _) x)
    have hL:1 ≤ L:=by exact_mod_cast g.count.property
    have hs(L':ℕ):= valueG (G:=G) g P h L' g.count; have hV:=hs m|>.1; have hA:= (hs m).2.2.1; have hX:=hs r|>.2.2.2.1; have hO:=hs r|>.2.2.2.2 r
    let F:= L^4*(ν/L); have hF:0≤ F:=by unfold F; positivity
    let y:=(E/L)^m
    have hy:0 ≤ y := by unfold y; positivity
    let H':= 2*(feed a η H D N k m/L^m)*((4/L)^(4-m)); let Q:=Lis.statue G r (m-1); have ht:F*y*(Q*A) ≤ s'*(w^4*A)/w^(m+1):=by
        let y':= aid G g.count m r a D η H N k; have hK:F*y*Q=y':=by unfold F y Q y' aid; field_simp
        have hG : y' ≤ s':=Finset.single_le_sum (f:=fun i=> aid G g.count i r a D η H N k) (fun i (_:i∈ Finset.Icc 1 3)=>by unfold aid; have hh:= Lis.statue_pos G r (i-1); positivity) (Finset.mem_Icc.mpr ⟨h₁,h₂⟩)
        calc
            _ = y'*A:=by rw [←hK]; ring
            _ ≤ s'*A:= mul_le_mul_of_nonneg_right hG ha
            _ ≤ _:=by rw [le_div_iff₀ (by positivity)]; have hp: w^(m+1) ≤ w^4:= pow_le_pow_right₀ hw (by omega); nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg hO ha)]
    rw [show _ / w^(m+1)=(C'/L*Z)/w^(m+1)+(s'*(w^4*A))/w^(m+1) from add_div ..]; change F*(H'*U₀+y*(v'+Q*A)) ≤ _
    rw [mul_add y,← add_assoc,mul_add F,← mul_assoc F y]; refine add_le_add ?_ ht
    refine (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hx' hy) _) hF).trans ?_
    have hI: lowP G m a D η H N k ≤ C' := by unfold fixP; exact (Finset.single_le_sum (f:=fun i=>lowP G i a D η H N k) (fun i hi=> by unfold lowP; have hX:=(hs i).2.1; positivity) (Finset.mem_Icc.mpr ⟨h₁,h₂⟩)).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i hi=> by unfold highP; positivity))
    refine le_trans (b:= lowP G m a D η H N k/L*U₀) ?_ ((mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hI (by positivity)) hU).trans_eq ?_); -- analyze
    · have hx:F*H'= ν*(2*feed a η H D N k m*4^(4-m))/L:= by unfold F H'; interval_cases m <;> norm_num1 <;> field_simp <;> ring -- proof heartbeat
      have he: F*y*(c'/L^3) ≤ ν*(E^m*c')/L:=by
           have hp:L≤L^m:= by nth_rw 1 [←pow_one L]; exact pow_le_pow_right₀ hL h₁
           have hh:E^m/L^m≤ E^m/L:=div_le_div_of_nonneg_left (by positivity) (by positivity) hp
           unfold y; rw [div_pow]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hF) (show 0≤ c'/L^3 from (by positivity))).trans_eq; unfold F; field_simp
      rw [mul_add F]; change F*(H'*U₀)+F*(y*(U₀*_)) ≤ _
      calc
        _ = F*H'*U₀ + F*y*(c'/L^3)*U₀ :=by ring
        _ ≤ F*H'*U₀ + ν*(E^m*c')/L*U₀:= add_le_add_right (mul_le_mul_of_nonneg_right he hU) _
        _ = _:=by rw [hx]; unfold lowP c'; ring
    unfold U₀; ring
end YM.MSbar.Parma
