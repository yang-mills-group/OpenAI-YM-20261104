import YM.WilsonCoeffUV.Root.Gain.Basis
/-!
# Position-root centering in polynomial pressure. Pre-length per piece.
Actual initial vertices with inverse Coat. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X Z D':ℝ}{P:Patch}
private lemma lamp_pure (i:Axis){f:E4→ℝ}(p:f ∈ exactDegree _ k): (fun x:E4=> x i • f x)∈ exactDegree ℝ (k+1):=by
   apply exact_of_smooth; · exact ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.mul (exact_smooth p _)).contDiffAt
   intro x t; rw [exact_scale p x t]; simp [pow_succ]; ring
private lemma lamp_slot (i:Axis){f:E4→ℝ}(p:f ∈ rangeLt _ k): (fun x:E4=> x i • f x)∈ rangeLt ℝ (k+1):=by
   obtain ⟨a,ha,h⟩ := Place.range_decompose p; rw [show (fun x:E4=> x i • f x)= ∑ j,fun x:E4=> x i • a j x from funext fun _=> by rw [h,Finset.sum_apply,Finset.sum_apply,Finset.smul_sum]]; apply Submodule.sum_mem; intro j _; exact exact_le_band (Nat.succ_lt_succ j.isLt) (lamp_pure _ (ha j))
lemma money (f:Cover→ℝ)(k:ℕ): Newt.piece k f∈ rangeLt _ (k+1):=by
    induction k generalizing f with
    | zero=> exact Place.exact_le_band (by omega) (exact_constant (f 0))
    | succ k ih=>
       let u (i:Axis) (x:E4):= x i • Newt.piece k (Newt.jump f i) (x+ -basis i)
       let c:= ((k:ℝ)+1)⁻¹
       rw [show Newt.piece (k+1) f=c • ∑ i,u i from funext fun x=> by rw [Newt.piece,Pi.smul_apply, Finset.sum_apply]; simp_rw [sub_eq_add_neg]; rfl]; apply Submodule.smul_mem; apply Submodule.sum_mem; intro i _; exact lamp_slot i (Place.band_shift (ih _) _)
lemma change_due (k:ℕ)(x:E4) : ∃ C:ℝ,0≤C∧∀ (f:Cover→ℝ)(B:ℝ), 0≤B→ (∀v:List Axis,v.length=k→‖Newt.iterate f v 0‖≤B)→‖Newt.piece k f x‖≤C*B:=by
   induction k generalizing x with
   | zero=> exact ⟨1,zero_le_one,fun f B _ ht=> by rw [one_mul]; exact ht [] rfl⟩
   | succ k ih =>
       choose C hc hx using ih; let A:= ((k:ℝ)+1)⁻¹; refine ⟨‖A‖*(∑ i:Axis,‖x i‖*C (x-basis i)),mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (hc _)),fun f B p H=>?_⟩
       rw [Newt.piece,norm_smul]; unfold A; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum _); intro i _; rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (hx _ _ B p fun v hv=> H (i::v) (by rw [List.length_cons,hv])) (norm_nonneg _)
-- corner value
abbrev Drip (P:Patch)(G:Gauge) := ropes Cover (Co P.L (Hooks G)) (Hooks G)
def sip (P:Patch)(Q:Drip P G)(w:Site P.L)(x:YForest G): Leg G:=fun i=> spring P.L Q (lift w+i.1,i.2) x
def breaks (P:Patch) (Q:Drip P G) (w:Site P.L) (x:YForest G) (k:ℕ): Place.Potential G:= fun u i=> coatC G fun j=> Newt.piece k (fun y:Cover=> sip P Q w x (waive y i j)) u
lemma stain (P:Patch)(Q:Drip P G)(w:Site P.L)(x y:YForest G)(k:ℕ): assay (breaks P Q w x k) y= Newt.piece k (fun z=> sip P Q w x (z,y.2)) (Pattern.xyz y.1):=by
    obtain ⟨v,j,rfl⟩:=every_stone y; unfold assay; rw [feather_at]; rfl
lemma breaks_in (P:Patch)(Q:Drip P G)(w:Site P.L)(x:YForest G)(k:ℕ): breaks P Q w x k∈ rangeLt _ (k+1):=by
    refine Place.vector_band (fun i u=>breaks P Q w x k u i) (fun i=>?_); exact Place.linear_band (coatC G).toContinuousLinearMap (k+1) (Place.vector_band _ (fun j=> money _ _))
lemma price_o {w:Site P.L}{Q:Drip P G}(p:Crank Q D s X)(l:List Axis)(hx:l.length ≤ D)(k:Hooks G)(x:YForest G): ‖Newt.iterate (fun z=>sip P Q w x (z,k)) l 0‖ ≤ X*speck P^(l.length+1)*Real.exp (-s*size x.1):=by
   have he:= p.2 l hx (lift w) 0 k x
   have hg : parentC P.L (lift w)=0:=by convert parent_pack (L:=P.L) ((0:Cover),w,()); simp only [castE,smul_zero,zero_add]
   unfold sip; rw [add_zero,hg,show Bank.terrain.gap 0 x.1=size x.1 from ?_,Nat.add_comm 1,div_eq_mul_inv,←inv_pow] at he; exact he
   change size (x.1-0)=_; rw [sub_zero]
lemma break_charge (G:Gauge)(k:ℕ): ∃ C:ℝ, 0≤C ∧ ∀ (P:Patch)(D:ℕ)(X s:ℝ)(Q:Drip P G),k ≤ D → Crank Q D s X→ ∀ w x, slideRank (k+1) (breaks P Q w x k)≤ C*X*speck P^(k+1)*Real.exp (-s*size x.1):=by
   classical
   choose C hc hx using change_due k
   let L : Lawn G.ColorIndex →L[ℝ]G.Color:= (coatC G).toContinuousLinearMap; let V:=Zest G (k+1); let A:= ∑ i∈V,C i
   have hA:0≤ A:= Finset.sum_nonneg fun _ _=> hc _; have ht:0≤ ‖L‖:=norm_nonneg _
   refine ⟨‖L‖*A,by positivity,fun P D X s Q h g w x=>?_⟩
   have hl:=speck_pos P; have he':=g.1
   let S:= X*speck P^(k+1)*Real.exp (-s*size x.1); have hp:0 ≤ S:=by unfold S; positivity
   rw [show _ * _ * Real.exp _= ‖L‖*(A*S) from by unfold S; ring]; apply slidek _ _ (by positivity); intro a ha; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro j
   apply (L.le_opNorm _).trans; apply mul_le_mul_of_nonneg_left _ ht; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro u
   exact (hx a (fun y => sip P Q w x (waive y j u)) S hp fun l hl=> ((price_o (w:=w) g l (hl.symm ▸ h) (coord j,u) x).trans_eq (by rw [hl]))).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>hc i) ha) hp)

def splint (P:Patch)(Q:Drip P G)(w:Site P.L)(x:YForest G)(D)(b:Fin (D+1)): Leg G:= if b.val<D then assay (breaks P Q w x b.val) else fun y=> Newt.tail D (fun z=> sip P Q w x (z,y.2)) y.1
lemma sipping (P:Patch)(Q:Drip P G)(w:Site P.L)(x:YForest G)(D:ℕ): sip P Q w x=∑ b:Fin (D+1), splint P Q w x D b:=by
   rw [Fin.sum_univ_castSucc, splint, if_neg (show ¬ (Fin.last D).val<D from lt_irrefl D)]; funext y; simp only [Pi.add_apply, Finset.sum_apply]; let f:=fun z:Cover=> sip P Q w x (z,y.2); change sip P Q w x y= (∑ b:Fin D,_)+Newt.tail D f y.1; rw [Newt.tail,Newt.take,← Fin.sum_univ_eq_sum_range];
   have he (b:Fin D): splint P Q w x D b.castSucc y= Newt.piece b.val f (Pattern.xyz y.1):=by rw [splint,if_pos (show b.castSucc.val<D from b.isLt),stain]; rfl
   simp_rw [he, add_sub_cancel]; rfl
lemma Wages.minus {F P: Leg G}(p: Wages F)(q:Wages P): Wages (F-P):=by
    obtain ⟨n,A,h,H⟩:=p; obtain ⟨m,C,x,X⟩:=q; refine ⟨n+m,A+C,add_nonneg h x,fun y=>?_⟩; refine (norm_sub_le ..).trans ((add_le_add (H y) (X y)).trans ?_); rw [add_mul]; unfold liftCost; gcongr <;> simp
lemma Wages.plus {F P:Leg G}(p:Wages F)(q:Wages P): Wages (F+P):=by
    rw [←sub_neg_eq_add]; refine p.minus ?_; obtain ⟨n,C,h,H⟩:=q; exact ⟨n,C,h,fun i=>by rw [Pi.neg_apply,norm_neg]; exact H _⟩
lemma Wages.sums {S:Finset U}{F: U→Leg G}(p:∀ i∈S,Wages (F i)):Wages (∑ i∈S,F i):= by
    classical
    induction S using Finset.induction_on with
    | empty=> exact ⟨0,0,le_rfl,fun i=> by simp⟩
    | insert a b e h=> rw [Finset.sum_insert e]; exact (p a (Finset.mem_insert_self ..)).plus (h fun i hi=>p i (Finset.mem_insert_of_mem hi))
lemma splints (P:Patch)(Q:Drip P G)(w:Site P.L)(x)(g:Crank Q D s X)(hp:0<s): ∀ b:Fin (D+1), Wages (splint P Q w x D b):=by
    have hg b (h:b ≠ Fin.last D): Wages (splint P Q w x D b):=by rw [splint,if_pos]; exact pays_assay (k:=b.val+1) _ (breaks_in P Q w x b.val); have he:b.val≠ D:= fun hv=>h (Fin.ext hv); omega
    intro b; by_cases h:b=Fin.last D; swap; · exact hg b h
    subst b
    let S:= Finset.univ.erase (Fin.last D); let F:=splint P Q w x D
    have he:= sipping P Q w x D
    have hf : F (Fin.last D)= sip P Q w x-∑ i∈S,F i:=eq_sub_of_add_eq ((Finset.add_sum_erase Finset.univ F (Finset.mem_univ _)).trans he.symm)
    change Wages (F _); rw [hf]; apply Wages.minus _ (Wages.sums (fun i hi=>hg i (Finset.mem_erase.mp hi).1)); let T:ℝ:=X/P.L.val
    have ht :0≤ T:= div_nonneg g.1 (by positivity)
    refine ⟨0,T,ht,fun i=>?_⟩; rw [liftCost,pow_zero]; apply (g.below (lift w+i.1,i.2) x).trans; apply mul_le_mul_of_nonneg_left _ ht; rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
lemma break_money (G:Gauge)(D:ℕ)(s:ℝ)(hs:0<s): ∃ C:ℝ,0≤C ∧ ∀ (P:Patch)(Q:Drip P G) (A:ℝ), Crank Q D s A →∀ (w:Site P.L) (x:YForest G)(b:Fin (D+1))(y),
     ‖splint P Q w x D b y‖≤ (C*A*(speck P)^(b.val+1)*Real.exp (-s*size x.1))*((1+(size y.1):ℝ)^D*Real.exp ((s/P.L.val)*size y.1)):=by
   let F (i:Fin (D+1)):= (4*((i.val:ℝ)+1))^i.val; let k:= (∑ i,F i)+Real.exp (8*s); have hK (i): 0≤F i:=by unfold F; positivity
   have hk' : Real.exp (8*s)≤k:= le_add_of_nonneg_left (Finset.sum_nonneg fun i _=> hK _)
   have hk :0≤ k:= (Real.exp_pos _).le.trans hk'
   refine ⟨k,hk,fun P Q A g w x b y=>?_⟩; let f (z:Cover):= sip P Q w x (z,y.2); let X (k:ℕ):= A*speck P^(k+1)*Real.exp (-s*size x.1); set q:= Real.exp ((s/P.L.val)*size y.1); have hq:1≤ q:= Real.one_le_exp (by positivity)
   have hp:=speck_pos P; have hv:= g.1; have ht : 0≤ X b.val:=by unfold X; positivity
   unfold splint; split
   next H=>
      rw [stain]; refine (Newt.component _ f ht (fun l h=> (price_o g _ (show l.length≤ D from by omega) y.2 x).trans_eq (by rw [h])) y.1).trans ?_
      change F b* _* X b.val≤ _; rw [mul_right_comm]
      exact mul_le_mul (by change F b * X b.val≤ _; unfold X; rw [show k*A*_= k*(A* speck P^(b.val+1)) by ring, mul_assoc k]; exact mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun i _=> hK i) (Finset.mem_univ b)).trans (le_add_of_nonneg_right (Real.exp_pos _).le)) ht) ((pow_le_pow_right₀ (by simp) H.le).trans (le_mul_of_one_le_right (by positivity) hq)) (by positivity) (by positivity)
   next H=>
      have hh: b.val=D:=by omega
      rw [hh]
      have he:= g.tag hs (lift w) y.1 y.2 x
      have hg : parentC P.L (lift w)=0:=by convert parent_pack (L:=P.L) ((0:Cover),w,()); simp only [castE,smul_zero,zero_add]
      dsimp only at he; rw [hg,show Bank.terrain.gap 0 x.1=size x.1 from (show size (x.1-0)=size x.1 by rw [sub_zero]),Nat.add_comm 1,div_eq_mul_inv,←inv_pow] at he
      refine he.trans ?_; change _ * _ * q * _≤ _*_
      rw [mul_comm A, show ((Real.exp _*A)*_)*_*q*_= ((Real.exp (8*s)*A)* speck P^(D+1)*Real.exp (-s*size x.1))*((1+(size y.1):ℝ)^D*q) from ?_]; gcongr
      unfold speck; ring
end YM.WilsonCoeffUV.Cosmos
