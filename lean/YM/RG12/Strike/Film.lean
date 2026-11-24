import YM.RG12.Strike.FirstPulse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
/-! # Analytic exterior Taylor coefficients at remote mark

Agreement of predifferentiated-layer rule with weighted Taylor on EACH exterior potential
and THEN vertex differentiation, including Taylor convolution when two exterior potential
lines. Spectator's exact Taylor clip identity at its own mark. Thus analyzing `frosted` really
tests the slots relevant for the first normalization criterion and involves no assumption
of its homogeneity or integration-by-parts, though not itself a scheme identification.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {S₀:Set R}{f g:R→ℂ} (h:IsOpen S₀)(hf:silk S₀ f) {x:R}(hx:x∈S₀) (n:ℕ) (y:R)
lemma fresco_read : fresco n f x y=((n.factorial:ℕ):ℂ)⁻¹ * fall (gauge n (fun l=>barrage f l x)) y:=rfl
include h hf hx
lemma winds : fresco n f x y=((n.factorial:ℕ):ℂ)⁻¹ * iteratedFDeriv ℝ n f x (fun _=>y):=(congrArg (fun t:ℂ=> ((n.factorial:ℕ):ℂ)⁻¹*t) (on_wind h hf hx n y)).symm
-- differentiated remote body (any order) at the marker. pull entirely via Fréchet to avoid
-- separate tensor slot expansion. One action derivative AND mark curls may be pulled repeatedly.
lemma fir (j:Axis4): hit j (fresco (n+1) f x) y=fresco n (hit j f) x y:=by
   have hf':=hf x hx
   have hd:=silken h hf j
   let p:=n+1; let G:=iteratedFDeriv ℝ p f x; let q(t:ℝ):Fin (n+1)→R:=fun _=>palette j y t
   let Y:Fin (n+1)→R:=fun _=>y;let e:Fin (n+1)→R:=fun _=>bar j;have hq : q 0=Y:=funext fun _=> born ..
   have he(_i:Fin p): (G.linearDeriv Y) e=∑ l:Fin (n+1), G (Function.update Y l (bar j)):=G.linearDeriv_apply ..
   have hu(i:Fin p): G (Function.update Y i (bar j))= iteratedFDeriv ℝ n (hit j f) x (fun _=>y):=by
      let v:=Fin.snoc (α:=fun _=>R) (fun _:Fin n=>y) (bar j)
      have he : Function.update Y i (bar j) = v ∘ Equiv.swap (Fin.last n) i:=by
         funext k; by_cases hk:k=i
         · subst k; simp [v,Function.comp_apply]
         by_cases ha:k=(Fin.last n)
         · subst k; simp only [Function.comp_apply, Equiv.swap_apply_left,Function.update_of_ne hk]
           cases i using Fin.lastCases with
           | last=> simp at hk
           | cast i=> simp only [Y,v,Fin.snoc_castSucc]
         rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne ha hk, Function.update_of_ne hk]
         cases k using Fin.lastCases with
         | last=> simp at ha
         | cast k=> simp only [Y,v,Fin.snoc_castSucc]
      let w: (R→L[ℝ]ℂ)→L[ℝ]ℂ:=ContinuousLinearMap.apply ℝ ℂ (bar j)
      have hh: hit j f =ᶠ[𝓝 x] w ∘ (fderiv ℝ f):=treads h hf hx j
      rw [he]; change iteratedFDeriv ℝ (n+1) f x _=_
      rw [hf'.iteratedFDeriv_comp_perm,iteratedFDeriv_succ_apply_right, (hh.iteratedFDeriv ℝ n).eq_of_nhds] -- order iteratedF...
      rw [w.iteratedFDeriv_comp_left (n:=ω) (hf'.fderiv_right le_top) le_top]; unfold v;rw [Fin.init_snoc, Fin.snoc_last]; rfl
   have hq' : HasDerivAt q e (0:ℝ):=hasDerivAt_pi.mpr (fun _=>drawing ..)
   let A(k:ℕ):= ((k.factorial:ℕ):ℂ)⁻¹
   have hi : HasDerivAt (fun t:ℝ=>A p * G (q t)) (A p*((∑ l:Fin (n+1),G (Function.update Y l (bar j))))) (0:ℝ):=by
     have hz := (hasDerivAt_const (0:ℝ) (A p)).mul ((show HasFDerivAt G (G.linearDeriv Y) (q 0) from hq.symm ▸ (G.hasFDerivAt Y)).comp_hasDerivAt 0 hq') -- casts
     rw [zero_mul,zero_add,he ⟨0,show 0 < p from Nat.succ_pos _⟩] at hz; exact hz
   unfold hit;rw [show fresco (n+1) f x ∘ palette j y=(fun t:ℝ=>A p * G (q t)) from funext fun t=> winds h hf hx _ _, hi.deriv]
   rw [winds h hd hx n y];simp_rw [hu]; simp only [sum_const,Fintype.card_fin,card_univ,nsmul_eq_mul] -- card order
   unfold A p; rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one];field_simp
-- sled for clips exactly evaluated after spatial stencil at 0
lemma lace (p:Poke): barrage (fresco n f x) p 0 = if p.length=n then barrage f p x else 0:=by
   -- iterate left? barrage p outer on tail inner; induction p choosing LAST wanted. use reverse recursion
   induction p using List.reverseRecOn generalizing n f with
   | nil=>
     simp only [barrage,List.length_nil];cases n with
     | zero=> rw [if_pos rfl,winds h hf hx]; simp only [Nat.factorial_zero,Nat.cast_one,inv_one,one_mul,iteratedFDeriv_zero_apply]
     | succ n=> simp only [fresco,essence,Complex.ofReal_zero,PiLp.zero_apply,zero_mul,sum_const_zero,mul_zero,ite_false,Nat.zero_ne_add_one] -- names
   | append_singleton l j he=>
     cases n with
     | zero=>
        rw [if_neg (by simp)]
        rw [show fresco 0 f x = fun _=>f x from funext fun y=>by rw [winds h hf hx]; simp, barrage_append]
        rw [show barrage (fun _:R=>f x) [j] = (0:R→ℂ) from funext fun y=>by unfold barrage hit; exact deriv_const ..]
        exact barrage_zero ..
     | succ n=>
        rw [List.length_append]; simp only [List.length_cons,List.length_nil, Nat.add_right_cancel_iff]
        rw [barrage_append,barrage_append,show barrage (fresco (n+1) f x) [j]=fresco n (hit j f) x from funext fun y=> fir h hf hx n y j, show barrage f [j]=hit j f from rfl]; exact he (silken h hf j) n -- he generalized f?
-- product rule with Taylor symbols, via ordinary one-dimensional line prices
private def read (f:R→ℂ)(x y:R)(t:ℝ):=f (t•y+x)
lemma fern : fresco n f x y= ((n.factorial:ℕ):ℂ)⁻¹* iteratedDeriv n (read f x y) 0:=by
   have H:Continuous (fun z:R=>z+x):=continuous_id.add continuous_const
   let s:= (fun z:R=> z + x) ⁻¹' S₀; have hs:IsOpen s:=h.preimage H
   obtain ⟨φ,A⟩:= leaf (shift f x) hs (fun z hz=> ContDiffAt.comp (g:=f) _ (hf _ (show z+x∈_ from hz)) (contDiffAt_id.add contDiffAt_const)) (show (0:R)∈s from (Set.mem_preimage.mpr (by simpa only [zero_add] using! hx)))
   have hv0:(0:R)∈s:= show (fun z:R=>z+x) 0∈ S₀ from show 0+x∈S₀ from (by simpa only [zero_add] using! hx) -- avoid
   let L:ℝ→L[ℝ]R:=(ContinuousLinearMap.id ℝ ℝ).smulRight y;have hv(t):L t=t•y:=rfl
   rw [←fresco_river, winds hs (f:=shift f x) (fun z hz=> (hf _ hz).comp z (contDiffAt_id.add contDiffAt_const)) hv0]
   rw [←(A.iteratedFDeriv ℝ n).eq_of_nhds]
   have hh : (⇑φ ∘ L)=ᶠ[𝓝 (0:ℝ)] read f x y:=by
      apply Filter.EventuallyEq.comp_tendsto A
        -- Provide Tendsto L and change
      have hp:L 0=0:=by rw [map_zero]
      exact hp ▸ L.continuous.tendsto 0
   rw [← hh.iteratedDeriv_eq n,iteratedDeriv_eq_iteratedFDeriv]
   rw [L.iteratedFDeriv_comp_right (φ.orders n) (i:=n) _ le_rfl]
   simp [hv, ContinuousMultilinearMap.compContinuousLinearMap_apply]
lemma vases (hg:silk S₀ g) : fresco n (f*g) x y=∑ i∈Finset.range (n+1),fresco i f x y*fresco (n-i) g x y:=by
   have ht(V:R→ℂ)(he:silk S₀ V): ContDiffAt ℝ (n:ℕ∞ω) (read V x y) 0:=by
      have hp : ContDiffAt ℝ (n:ℕ∞ω) (fun t:ℝ=>t•y+x) 0:= (contDiffAt_id.smul contDiffAt_const).add contDiffAt_const
      exact ContDiffAt.comp (g:=V) (f:=fun t:ℝ=>t•y+x) 0 (((by simpa using! (he _ hx):ContDiffAt ℝ ω V ((fun t:ℝ=> t•y+x) 0))).of_le le_top) hp
   let V:= read f x y; let W:= read g x y
   rw [fern h (show silk S₀ (f*g) from fun _ h' => (hf _ h').mul (hg _ h')) hx,show read (f*g) x y=V*W from rfl,iteratedDeriv_mul (ht f hf) (ht g hg),mul_sum]
   refine sum_congr rfl (fun i hi=>?_);rw [fern h hf hx, fern h hg hx]
   have hcc : (↑(n.choose i ):ℂ) * ((↑i.factorial):ℂ) * ((↑(n-i).factorial):ℂ)=(↑n.factorial:ℂ):=by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
   -- clear
   have hz(k:ℕ): ((↑(k.factorial):ℂ))≠0:=by exact_mod_cast (Nat.factorial_pos k).ne'
   field_simp [hz];linear_combination ((iteratedDeriv i (read f x y) 0) * (iteratedDeriv (n-i) (read g x y) 0))*hcc
-- any leg local Taylor at potential slots, hit specified in V3.
def opened (D:List Axis4)(n:ℕ)(f:R→ℂ)(x:R)(y:R):ℂ:=barrage (fresco (n+D.length) f x) D y
lemma steal (D:Poke):opened D n f x y=fresco n (barrage f D) x y:=by
   induction D using List.reverseRecOn generalizing f with
   | nil=> rfl
   | append_singleton l j hl=>
     unfold opened
     rw [show n+(l++[j]).length=n+l.length+1 by simp [add_assoc]]
     rw [barrage_append,show barrage f (l++[j])=barrage (barrage f [j]) l from funext fun y=>barrage_append .. ,show barrage (fresco (n+l.length+1) f x) [j]=fresco (n+l.length) (hit j f) x from funext (fun y=>fir h hf hx (n+l.length) y j),show barrage f [j]=hit j f from rfl]; exact hl (silken h hf j)
variable (W V:Foil)(T U:Poke)(i j:Axis4)(D L:Poke)
-- true derivatives of opened kernel at puncture for polar Taylor. identify all legs
omit h hf hx in
lemma hem (p:Poke){x:R}(hx:x≠0):barrage (leg W T i D) p x=barrage (cloud W T i) (p++D) x:=by
    rw [barrage_append]
    apply barrage_local punct_open (x:=x) hx _
    intro y hy; rw [ridges W T D ..]; swap;exact hy; unfold leg; simp only [List.append_assoc,tube]
omit h hf hx in
lemma weave (n:ℕ){x:R}(hx:x≠0):fresco n (leg W T i D) x y = opened D n (cloud W T i) x y:=by
   rw [steal punct_open (cloud_silk W T i) hx]
   unfold fresco; simp_rw [hem W T i D _ hx,barrage_append]
omit h hf hx in
theorem loom {x:R}(hx:x≠0):
    rainJet n (leg W T i D * leg V U j L) x y = ∑ p∈Finset.range n, ∑ b∈Finset.range (p+1), opened D b (cloud W T i) x y * opened L (p-b) (cloud V U j) x y:=by
   unfold rainJet;simp_rw [vases punct_open (Garden.lineage W T i D).openSite hx _ y ((Garden.lineage V U j L).openSite), weave y W T i D _ hx,weave y V U j L _ hx] -- argument order
end YM.RG12.Strike
