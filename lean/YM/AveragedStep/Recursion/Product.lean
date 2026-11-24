import YM.AveragedStep.Recursion.Present
/-!
# Conditional joint matching recovery on any independent Azure coefficient solution

Must next produce U, read against actual constructed object and tackle
postcut windows and other normalization conventions. The induction here is
NOT running the Horizon obstruction backwards: for all finite monomials
separately with activated length demands. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
variable {c f:Side}{G:Gauge}{S:StepData c f}{A:ChartRatio G}(F:Forest S.ratio)
variable (Q:Cuff S.patch S.kernel A)
lemma dirt_locked (x:Site c)(τ:ℝ)(U:Azure A F)(d:ℕ){w}{i:Ink G c f}(he:i.1.elim (fun j=> j∈F.trunks) (fun _=>False))(hV:i∈w) (z:TopologyQ F G):dirt F Q x τ d z U w = 0 :=by
 rcases i with ⟨i,j⟩; rcases i with i|i
 · have h0:=chamber_pin F A Q x τ z i he
   have hs(n:ℕ): U.trial n (hands F Q x τ z) w=0:=U.fixed he j hV ..
   unfold dirt Azure.span
   simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hs,mul_zero,Finset.sum_const_zero,sub_zero,sample,mon]
   rw [List.prod_eq_zero]; apply List.mem_map.mpr ⟨(Sum.inl i,j),hV,?_⟩; rw [h0]; rfl
 exact False.elim he
lemma dirt_perm (x:Site c)(τ:ℝ)(U:Azure A F)(d:ℕ){w v:Lips G c f}(h:List.Perm w v)(z):dirt F Q x τ d z U w=dirt F Q x τ d z U v:=by
 unfold dirt; simp only [Pi.sub_apply,U.span_perm _ h]; congr 1; exact List.Perm.prod_eq (h.map _)
lemma clips_perm {w v:Lips G c f}(h:List.Perm w v): clips w=clips v:=List.Perm.sum_eq (h.map _)
lemma lens_perm {w v:Lips G c f}(h:List.Perm w v)(S:StepData c f)(a:ℝ)(x:Site f):lens S a x w=lens S a x v:=by
 unfold lens steps; rw [List.Perm.sum_eq (h.map _)]
lemma dirt_terminal (x:Site c)(τ:ℝ)(U:Azure A F)(d:ℕ){w:Lips G c f}(h:clips w=0)(z):dirt F Q x τ d z U w=0:=by
 simp only [dirt,Pi.sub_apply,Azure.span,Finset.sum_range_succ' (fun i=> _) d,Pi.add_apply,Finset.sum_apply, Pi.smul_apply, smul_eq_mul,U.cutoff h]
 simp
lemma clips_by_cases (w:Lips G c f): clips w=0∨∃ (i:Edge (Site f))(j:G.ColorIndex)(v:Lips G c f), List.Perm w ((Sum.inl i,j)::v):=by
 induction w with
 | nil=>left;rfl
 | cons i w ih=>
   rcases i with ⟨i,j⟩
   cases i with
   | inl i=> exact Or.inr ⟨i,j,w,List.Perm.refl _⟩
   | inr i=>
     rcases ih with h|⟨i',j',v,h⟩; · left; rw [clips_cons,h]; rfl
     exact Or.inr ⟨i',j',(Sum.inr i,j)::v,(h.cons _).trans (.swap ..)⟩

section present
variable {P:Patch}{K:KernelChoices}(D':Cuff P K A)(hA:LocalRatio A)(hS:P.Branches K G){L D δ:ℝ}(hQ:Cadence D' L D δ)
omit F Q in
lemma covered_zero (d k:ℕ):Covered D' d 0 k:=by
 refine fun a ha=> ⟨0,0,le_rfl,Eventually.of_forall fun τ {_ _} S F hP hK h hh x u hu hx U=>?_⟩
 intro C w hw hI
 simp only [lessons,dirt_terminal F C x τ U d (Nat.eq_zero_of_le_zero hI),mul_zero, report,integral_zero,zero_mul,abs_zero,le_refl]
omit F Q in
include hA hS hQ in
lemma covered_all (d n k:ℕ):Covered D' d n k:=by
 induction d using Nat.strong_induction_on generalizing n k with
 | h d ih=>
 induction n generalizing k with
 | zero=>exact covered_zero D' d k
 | succ n hn=>
   intro b hb
   let E:=Classical.choice (activated G P K A)
   let a:ℝ:=min (b/(d+1:ℝ)) (E.η/2/(d+1:ℝ))
   have hap:0<a:=lt_min (by positivity) (by have :=E.available; positivity)
   have hab:a*(d+1:ℝ)≤b:= le_div_iff₀ (by positivity) |>.mp (min_le_left ..)
   have hae:a*(d+1:ℝ)≤E.η/2:= le_div_iff₀ (by positivity) |>.mp (min_le_right ..)
   obtain ⟨V,r,hV,HV⟩:=hn k a hap
   let m(j:Fin d):=d-(j.val+1)
   obtain ⟨X,s,hX,HX⟩:=advance D' (k:=fun _:Fin d=> k+d+1) (n:=fun _=> k+d+1) hap (d:=m) (fun i=> ih (m i) (by have h:=i.isLt; unfold m; omega) (k+d+1) (k+d+1))
   obtain ⟨Z,u,hZ,HZ⟩:=invoices D' hA hS hQ a hap d k
   obtain ⟨U,hU,HU⟩:= shy_friends A P K k
   choose C hC HC using (fun n=> joy_leap A P K n)
   let w:=|E.μ*((↑(keyMask G):ℝ)*countCost (E.η-E.η/2))|
   let y:=reachBit P d a
   let q:=r+s+u
   let T:=V+X+Z
   let g:= (U+(∑ p∈active d,C p)+1)*T
   have hG:0 ≤ g:=by unfold g T; have : 0 ≤ ∑ p∈active d,C p:=Finset.sum_nonneg (fun i _=> hC _); positivity
   refine ⟨g*w*y,q,by have hy:0<y:=Real.exp_pos _; unfold w; positivity,?_⟩
   filter_upwards [HV,HX,HZ,eventually_ge_atTop (1:ℝ)] with τ hV' hX' hZ' hT c f S F hP hK hz hS' x φ hf hφ Blue Q' L' hl lh
   let o:=S.ratio.embed x
   let M:= lessons F Q' x τ φ Blue
   have hCOV:Fund (S:=S) (τ:=τ) (a:=a) o (M d) d n k T q := (authorized D' hV' hT hV (by unfold T; linarith) (by unfold q; omega)) S F hP hK hz hS' x φ hf hφ Blue
   have hTOD (j)(hi:j∈active d): Fund (S:=S) (τ:=τ) (a:=a) o (M (d-j)) (d-j) (k+d+1) (k+d+1) T q :=by
      obtain ⟨hp,he⟩:= (on_tape ..).mp hi
      let j':Fin d:=⟨j-1,by omega⟩
      have hv:Ticket D' a τ (m j') (k+d+1) (k+d+1) T q:= authorized D' (hX' j') hT hX (C:=T) (r:=q) (by unfold T; linarith) (by unfold q; omega)
      have h:j'.val+1=j:=by unfold j'; dsimp; omega
      unfold m at hv; rw [h] at hv
      exact hv S F hP hK hz hS' x φ hf hφ Blue
   have hlens:0≤g*w*y*stale τ d q*lens S b o L':=by have :=lens_pos S b o L';have :=stale_pos hT d q;have hy:0<y:= Real.exp_pos _; unfold w; positivity
   change |M d L'| ≤ _
   obtain hh|⟨i,j,V',hp⟩:=clips_by_cases L'; · simp only [M, lessons,dirt_terminal _ _ _ _ _ _ hh,mul_zero, report,integral_zero,abs_zero]; exact hlens
   by_cases hi:i∈F.trunks
   · have he:(Sum.inl i,j) ∈ L':= hp.mem_iff.mpr List.mem_cons_self
     simp only [M, lessons,dirt_locked _ _ _ _ Blue d (i:=(Sum.inl i,j)) (show _ from hi) he,mul_zero,report,integral_zero,abs_zero]; exact hlens
   let l:Key F G:=(⟨i,hi⟩, j)
   have hp:List.Perm L' (fkey F l :: V'):=hp
   have ht0:V'.length+1 ≤ k:=by simpa only [hp.length_eq,List.length_cons] using hl
   have hP':pop (fkey F l) =1:=rfl
   rw [clips_perm hp,clips_cons,hP'] at lh
   have ht:clips V' ≤ n:=by omega
   have hM: M d L'=M d (fkey F l :: V'):=congrArg (report F (τ^2) x) (funext fun z=> congrArg (fun a=>φ z.2*a) (dirt_perm F Q' x τ Blue d hp z))
   have H(i:Key F G): |offer (M d) (weigh F A i V')| ≤ (g*stale τ d q)*coupon S a d o (fkey F i).1 V':=by
      have hb:S.patch.Branches S.kernel G:=by rw [hP,hK]; exact hS
      apply row F o M hT hap (B:=T) (by unfold T; positivity) ht0 ht i hCOV hTOD (HU S F hP hK hb i V' (by omega)) (fun i' _=> HC i' S hP hK (fkey F i) V')
      have hn: Invoice D' a τ d V'.length i.2 T q:= Invoice.lift D' (B':=T) (q':=q) (hZ' V'.length i.2 (by omega)) hT hZ (by unfold T; linarith) (by unfold q; omega)
      exact ⟨_, lessons_shift F Q' x τ φ hb hf Blue i V' d, hn S F hP hK hz x φ hf hφ V' rfl i.1⟩
   subst P K
   rw [hM,lens_perm hp S b]
   refine (discharge F o M hap E hS' hab hae (mul_nonneg hG (stale_pos hT ..)) H l).trans_eq ?_
   dsimp only [w,y,o]; ring
end present
end YM.AveragedStep.SD
