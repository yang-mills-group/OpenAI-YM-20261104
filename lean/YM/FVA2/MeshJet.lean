import YM.FVA2.LineJet
/-!
# Leading rank engineering fit for an actual lattice Section symbol

Highest free bidegree via truncated Taylor of *one power per leg*.
This tests all off-shell potential polynomials at these dimensions;
We don't pretend that dropping off-shell stencils after Wick cancellation
would preserve the estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.FVA2.Plate
open Filter Topology Set Function MeasureTheory
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book
open MS.Cylinder MS.Plane MS.Plane.Wire MS.Tone MS.Tone.Frame MS.Color
open RG PertExtension MvPolynomial MS.Theater
open Next.Foundations Labels
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{d k n:ℕ}
local notation "W"=>Lattice.Cover
local notation "print"=> YM.PertExtension.Heat.Ray.print
local notation "ℓ"=> Legs (Lane4 G)
local notation "⚙" => Theater.orbit G
local infix:70 " ⋆ " => product DotFlip
lemma combiner (μ:ℕ)(A B:Pol G) : ∀ k≤μ, tier k (A*B)= ∑ i∈Finset.range (k+1),tier i A*tier (k-i) B := by -- remove n
   intro k _; induction A using MvPolynomial.induction_on' with
   | monomial a c=> induction B using MvPolynomial.induction_on' with
     | monomial b q=>
       let w:= Labels.generation (G:=G); let ha:= isWeightedHomogeneous_monomial w a c (m:=Finsupp.weight w a) rfl
       let hb:= isWeightedHomogeneous_monomial w b q (m:=Finsupp.weight w b) rfl; let t:= a.sum fun x n=>n* w x; let u:= b.sum fun x n=>n*w x; have h₁:t=Finsupp.weight w a:=rfl; have h₂:u=Finsupp.weight w b:=rfl
       unfold tier; by_cases h:t+u=k; swap
       · rw [(ha.mul hb).weightedHomogeneousComponent_ne k (by omega)]; symm; exact Finset.sum_eq_zero (fun i hi=>by by_cases h:i=t; rw [hb.weightedHomogeneousComponent_ne (k-i) (by replace hi:= Finset.mem_range.mp hi; omega),mul_zero]; rw [ha.weightedHomogeneousComponent_ne i (by omega),zero_mul]) -- shadow tactic
       rw [Finset.sum_eq_single t]; swap; · intro i _ hi; rw [ha.weightedHomogeneousComponent_ne i (by omega),zero_mul]
       swap; · intro hi; exact (hi (Finset.mem_range.mpr (by omega))).elim
       rw [ show k-t=u by omega,h₂,hb.weightedHomogeneousComponent_same, h₁,ha.weightedHomogeneousComponent_same,show k=_ from (h.symm.trans (congr_arg₂ (·+·) h₁ h₂)),(ha.mul hb).weightedHomogeneousComponent_same ]
     | add x y hx hy=> simp_rw [mul_add,map_add,mul_add,hx,hy,Finset.sum_add_distrib]
   | add x y hx hy=> simp_rw [add_mul,map_add,add_mul,hx,hy,Finset.sum_add_distrib]

private def σ (t:ℝ) (z: Lane4 G) : ℂ:= match z with
   | (((some i,false),_),p)=> delay (t • p) i
   | _=> 1
private lemma taxed (z: Lane4 G) : ContDiff ℝ ∞ (fun t=> σ t z) := by rcases z with ⟨⟨⟨_|a,_|_⟩,s⟩,p⟩ <;> first| exact contDiff_const| exact delay_smooth ..
private lemma σ0 (z: Lane4 G): σ 0 z=1:= by rcases z with ⟨⟨⟨_|a,_|_⟩,s⟩,p⟩ <;> simp [σ,delay_zero] -- redundant
private abbrev ψ (F: Law G) (w:ℓ)(t:ℝ):= fieldVal F (ray w) t
-- no notation hazard: abbreviation w parentheses explicit for repeated access
private def meter (p:Page G) (w:ℓ) (t:ℝ):ℂ:=  (((t:ℂ)^w.length)*(w.map (σ t)).prod) * ψ (buzz G p).val w t
private lemma smooth_scatter {A: Type} (p:Sector A) (w:Legs A) (F:ℝ→Shared A ℂ)(H:∀ v x,Split v x w→ ContDiff ℝ ∞ (fun t:ℝ=> F t v x)): ContDiff ℝ ∞ (fun t=> scatter p w (F t)):= by
   induction w generalizing F with| nil=>exact H _ _ .nil| cons i w ih=> exact ih (fun t v x=> F t (i::v) x+ _ * F t v (i::x)) (fun v x h=> (H _ _ h.left).add (contDiff_const.mul (H _ _ h.right)))
private lemma scatter_reads {A: Type} (p:Sector A) (w:Legs A) (F:ℝ→Shared A ℂ)(H:∀ v x,Split v x w→ ContDiff ℝ ∞ (fun t:ℝ=> F t v x)): reading k (fun t=>scatter p w (F t))=scatter p w (fun v x=>reading k (fun t=> F t v x)):= by
   induction w generalizing F with| nil=> rfl| cons i w ih=>
       let f (t:ℝ) v x := F t (i::v) x+( cross (p i) (degree p v):ℂ)*F t v (i::x); change reading k (fun t=> scatter p w (f t))= _; rw [show reading k (fun t=> _) = _ from ih f (fun v x h=> ContDiff.add (H _ _ h.left) (contDiff_const.mul (H _ _ h.right))),scatter_cons _ i w]; unfold f; exact scatter_congr p _ _ _ (fun l r h=> by rw [ read_add (H _ _ h.left) (contDiff_const.mul (H _ _ h.right)), read_const ])
private lemma raw_prod (p q:Page G) (w:ℓ)(t:ℝ): ψ (buzz G (p*q)).val w t = scatter DotFlip w (fun v x=> ψ (buzz G p).val v t * ψ (buzz G q).val x t):= by rw [map_mul, Theater.darkM]; unfold ψ fieldVal; simp_rw [ ray_go,scattered]; exact scatter_move _ (fun i => (i.1,t • i.2)) (fun _=>rfl) w -- args
private lemma passing (p q:Page G)(w:ℓ)(t:ℝ): meter (p*q) w t=scatter DotFlip w (fun v x=> meter p v t * meter q x t):= by
   unfold meter; rw [raw_prod,show ∀ (F:Shared (Lane4 G) ℂ) (u:ℂ),u*scatter DotFlip w F=scatter DotFlip w (u • F) from fun F u=> (map_smul ( allocate DotFlip w ) u F).symm]; apply scatter_congr DotFlip _; intro a b h; simp only [Pi.smul_apply,smul_eq_mul];
   rw [ show w.length=a.length+b.length from (split_length h).symm,pow_add, show (w.map (σ t)).prod=(a.map (σ t)).prod * (b.map (σ t)).prod by simpa only [List.map_append,List.prod_append] using (((split_perm h).map (σ t)).prod_eq).symm ]; ring
private lemma line_smooth (T:Page G) (w:ℓ): ContDiff ℝ ∞ (ψ (buzz G T).val w):= by
   induction T using MvPolynomial.induction_on generalizing w with
   | C c=> unfold buzz ψ; rw [aeval_C,Theater.cash1 ]; cases w <;> exact contDiff_const
   | add p q hU hV=> rw [map_add]; exact (hU w).add (hV w)
   | mul_X p i ih=>
                     rw [funext (raw_prod _ _ w)]; refine smooth_scatter _ _ _ (fun v x _ => ContDiff.mul (ih v) ?_);
                     unfold buzz; rw [aeval_X]; rcases x with _|⟨⟨a,p⟩,_|_⟩ <;> try exact contDiff_const
                     change ContDiff ℝ ∞ (fun t:ℝ=> shine _ _ _ (a,t • p))
                     unfold shine; refine (bankForm ..).mul ?_; unfold curl; refine ContDiff.sum fun x _=> ?_; unfold paywave; dsimp only; exact (contDiff_const.mul (bankForm p (bornv (knot (front i.1.plaq) x)))).mul contDiff_const
private lemma gaugeTag (w:ℓ) : ContDiff ℝ ∞ (fun t:ℝ=> (w.map (σ t)).prod):= by induction w with| nil=>exact contDiff_const| cons i w IH=> exact (taxed i).mul IH
private lemma met_smooth (P:Page G)(w:ℓ): ContDiff ℝ ∞ (meter P w):= ((Complex.ofRealCLM.contDiff.pow _).mul (gaugeTag w)).mul (line_smooth _ _)
private lemma multiply_shift (w:ℕ)(f:ℝ→ℂ)(h:ContDiff ℝ ∞ f)(k:ℕ): reading k (fun t:ℝ => (t:ℂ)^w*f t)= if w≤k then reading (k-w) f else 0:= by
   rw [read_mul (f:=fun t:ℝ=> (t:ℂ)^w) (Complex.ofRealCLM.contDiff.pow _) h]; have ht (i:ℕ): reading i (fun t:ℝ=> (t:ℂ)^w)= if w=i then 1 else 0:=by simpa only [Complex.real_smul,Complex.ofReal_pow,mul_one] using read_pow (j:=i) (1:ℂ) w
   simp_rw [ht]; split_ifs with H; swap; · refine Finset.sum_eq_zero (fun x hx=>?_); rw [if_neg (by obtain h:=Finset.mem_range.mp hx; omega),zero_mul]
   rw [ Finset.sum_eq_single w (fun i hi h=>by rw [if_neg (Ne.symm h),zero_mul]) (fun h=>by obtain h:=mt Finset.mem_range.mpr h; omega),if_pos rfl,one_mul ]
private def AllA (w:ℓ): Prop:=∀ i∈w,∃ a:Axis,i.1.1=Landau.gauge a
private lemma atSum {w:ℓ} (h:AllA w): fieldDim wfield w=(w.length:ℤ):= by
    induction w with| nil=>rfl| cons a w ih=> rw [field_cons,ih fun i hi=>h _ (by simp [hi])]; obtain ⟨v,hv⟩:=h a (by simp); rcases a with ⟨⟨a,s⟩,q⟩; change a=_ at hv; subst a; simp; rw [show wfield (Landau.gauge v,s)=1 from rfl]; ring
private lemma born_l (a:Beast G)(k: Branch G Axis)(p:QP)(h:∀x,k.1≠Landau.gauge x): beacon a (k,p)=0:= by unfold beacon shine; rw [curl_off p _ _ _ h,mul_zero]
private lemma pure_rw {v:ℓ}(P:Page G) (h:¬ AllA v) : ψ (buzz G P).val v=fun _=>0:= by
   induction P using MvPolynomial.induction_on generalizing v with
   | C x=> unfold buzz; rw [aeval_C,Theater.cash1]; cases v; exact (h (by intro i hi; cases hi)).elim; rfl
   | add x y hx hy=> funext t; rw [map_add]; change ψ (buzz G x).val v t + ψ (buzz G y).val v t=0; rw [hx h, hy h, add_zero]
   | mul_X p i ih=>
       funext t; rw [raw_prod]; let X (l r:ℓ) := ψ ( buzz G p).val l t * ψ (buzz G (MvPolynomial.X i)).val r t; -- clean
       refine (scatter_congr DotFlip v X 0 (fun l r h' => ?_)).trans (map_zero (allocate ..)); by_cases hv:AllA r; · unfold X; rw [ih (by intro g; apply h; intro i hi; rcases List.mem_append.mp ((split_perm h').mem_iff.mpr hi) with hi|hi; exact g i hi; exact hv _ hi),zero_mul]; rfl
       unfold X; rw [show buzz G (MvPolynomial.X i)= leadS i from aeval_X ..]; rcases r with _|⟨⟨a,p⟩,_|_⟩; exact (hv (by intro i hi; cases hi)).elim; exact mul_eq_zero_of_right _ (show beacon i (a,t • p)= _ from (born_l i a (t • p) (fun x h=>hv (by intro j hj; rw [List.mem_singleton.mp hj]; exact ⟨x,h⟩)))); exact mul_zero _

private lemma const_sh (k:ℕ) (c:ℂ): reading k (fun _:ℝ=>c)=if k=0 then c else 0:= by simpa only [pow_zero,one_smul,eq_comm] using read_pow (j:=k) c 0
private lemma tier_C (s:ℕ)(c:ℂ): tier s (C c:Pol G)=if s=0 then C c else 0:= by unfold tier; split; · next h=> rw [h]; exact (MvPolynomial.isWeightedHomogeneous_C ..).weightedHomogeneousComponent_same
                                                                                next h=> exact (MvPolynomial.isWeightedHomogeneous_C ..).weightedHomogeneousComponent_ne s h
private lemma at_zero (a:Beast G)(d:ℕ): tier 0 (print d (X a)) =0 := by rw [print_X,map_sum]; apply Finset.sum_eq_zero; intro j _; rw [ map_smul, tier_X, if_neg (by unfold Labels.generation; omega),smul_zero ]
private lemma all_tokens (P:Page G)(w:ℓ) (d:ℕ): ∀ k≤d, Theater.orbit G (tier k (print d P)) w= reading k (meter P w) := by
   induction P using MvPolynomial.induction_on generalizing w with
   | C c=>
        intro k hk; rw [show print d (C c : Page G)=C c from AlgHom.commutes _ _,tier_C ]; rcases w with _|⟨a,w⟩
        · rw [show meter (C c : Page G) []=fun _=>c from funext (fun i=>by unfold meter ψ fieldVal buzz; rw [aeval_C,Theater.cash1]; simp only [List.length_nil,pow_zero,List.map_nil,List.prod_nil,one_mul]; rfl),const_sh]
          split <;> first| exact congr_fun (Theater.cus c) [] | (rw [map_zero]; rfl)
        ·
            rw [show meter (C c : Page G) (a::w)=fun _=>0 from funext fun i=>by simp [meter,ψ,fieldVal,ray_go,buzz,Theater.cash1,coin]]
            simp only [const_sh,ite_self]; split; exact congr_fun (Theater.cus c) _; rw [map_zero]; rfl
   | add x y hx hy=>
         intro k hk
         have he : meter (x+y) w=fun t=>meter x w t+meter y w t:= by funext; unfold meter; rw [map_add]; unfold ψ fieldVal; simp [mul_add]
         rw [map_add,map_add,map_add,Pi.add_apply,hx w k hk,hy w k hk,he,read_add (met_smooth x w) (met_smooth y w)]
   | mul_X p a ih=>
       intro k hk; let x:= X (R:=ℂ) a; have hX (v:ℓ) (k:ℕ)(hk:k≤d): Theater.orbit G (tier k (print d x)) v=reading k (meter x v):= by
           by_cases hv:∃ (i:Axis)(p:QP)(c:G.ColorIndex), v=[waveForm p i c]; swap
           · rw [off_lanes a k d v hv]; rw [show meter x v=fun _=>0 from funext fun t=>?_]; simp only [const_sh,ite_self]; unfold meter; apply mul_eq_zero.mpr; right; unfold buzz x; rw [aeval_X]; rcases v with _|⟨⟨z,p⟩,_|_⟩; swap; exact born_l a z (t • p) (fun i h=>hv ⟨ i,p,z.2,congr_arg (fun a:Landau.Atom Axis=> [((a,z.2),p)]) h⟩)
             all_goals rfl
           obtain ⟨i,p,c,rfl⟩ := hv; have h : meter x [waveForm p i c]=fun t:ℝ=> (t:ℂ)^1*(delay (t • p) i*beacon a (waveForm (t • p) i c)):= by unfold meter List.length; funext t; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,x,buzz,aeval_X]; rw [mul_assoc]; rfl
           let f (t:ℝ):=delay (t • p) i*beacon a (waveForm (t • p) i c); have he : ContDiff ℝ ∞ f:= (delay_smooth _ _).mul (?_); swap; · let H:= line_smooth (X a) [waveForm p i c]; unfold buzz at H; rw [aeval_X] at H; exact H
           rw [h,multiply_shift _ f he k]; rcases k with _|k; · unfold x; rw [at_zero,map_zero,if_neg (by omega)]; rfl
           rw [if_pos (by omega),Nat.add_sub_cancel]; exact ray_atom _ _ _ _ _ _ hk -- syntax
       let S := fun (t:ℝ) (l r:ℓ)=> meter p l t * meter x r t
       have ht : ∀ i≤ k,∀ w, Theater.orbit G (tier i (print d p)) w= reading i (meter p w):= fun i hi w=> ih w i (hi.trans hk)
       rw [funext (passing p x w), show print d (p*x)=_ from map_mul (print d) p x, combiner k (print d p) (print d x) k k.le_refl, map_sum, Finset.sum_apply, show reading k (fun t=> scatter DotFlip w ( S t ))=_ from scatter_reads _ w S (fun v x' _=> (met_smooth p v).mul (met_smooth x x'))]; simp_rw [bags,scattered]
       -- swap sums
       let A (i:ℕ) (v z:ℓ):= Theater.orbit G (tier i (print d p)) v * Theater.orbit G (tier (k-i) (print d x)) z; let R := Finset.range (k+1); rw [ show ∑ i∈R, scatter _ w (A i) = _ from Eq.symm (map_sum (allocate DotFlip w) A R) ]; refine scatter_congr (hands G) w _ _ fun v y _=>?_ ; simp only [Finset.sum_apply]; unfold A S; rw [read_mul (met_smooth ..) (met_smooth ..)]; apply Finset.sum_congr rfl; intro i hi; rw [ht _ ?_ _,hX y _ (by omega)]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
private lemma sweepOut {n:ℕ}{c:ℂ}{f g:ℝ→ℂ} (hf: ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g)(hg0: g 0=1)(h : ∀ i:ℕ,i≤ n→ reading i (fun t=>g t * f t)= if i=n then c else 0) : Rest f n c:= by
   have he (i:ℕ)(hi:i≤n) : reading i f=if i=n then c else 0:= by
       induction i using Nat.strong_induction_on with
       | h i ih=>
       rw [← h i hi,read_mul hg hf,Finset.sum_eq_single_of_mem 0 (by simp)]; · simp [reading,hg0]
       intro k hk hK; have h1:i-k < i := by obtain h:= Finset.mem_range.mp hk; omega
       rw [ih _ h1 (h1.le.trans hi),if_neg ((lt_of_lt_of_le h1 hi)).ne,mul_zero]
   exact ⟨ hf,fun i=>by omega,fun i hi=> by rw [he i (by omega)]; simp⟩

section cut
variable {P: Page G}{d h:ℕ}{q:Labels.Pol G}
theorem pullJet (hH:h≤d)(hQ: PertExtension.Heat.Ray.clipped d P=q)(hu: MvPolynomial.IsWeightedHomogeneous Labels.generation q h): MS.Lifting.Face wfield (buzz G P).val (Theater.orbit G q) h false:= by
   intro w _; have hT (i:ℕ)(hi:i≤h): reading i (meter P w)= if i=h then Theater.orbit G q w else 0:= by
       rw [← all_tokens P w d i (hi.trans hH), ← tier_capRead d _ i (hi.trans hH), show capRead d ( print d P )=q from hQ ]; unfold tier; by_cases h:i=h; rw [h,hu.weightedHomogeneousComponent_same,if_pos rfl]; rw [hu.weightedHomogeneousComponent_ne i h,map_zero, if_neg h]; rfl
   by_cases hA : AllA w; swap; · obtain hv:= pure_rw P hA; change Rest (ψ _ _) _ _; rw [hv, ← show reading h (meter P w)= _ from (hT h h.le_refl).trans (if_pos rfl), show meter P w=fun _=>0 from funext (fun t=> by unfold meter; rw [hv,mul_zero]), const_sh,ite_self ]; exact Rest.zero _
   rw [atSum hA]; let f:= ψ (buzz G P).val w; let g (t:ℝ):=(w.map (σ t)).prod
   have he : meter P w=fun t:ℝ=> (t:ℂ)^w.length*(g t*f t):= funext fun x=> mul_assoc ..
   simp_rw [he,multiply_shift _ (fun t=>g t*f t) ((gaugeTag w).mul (line_smooth P w))] at hT
   by_cases hw:w.length≤h; swap; · refine ⟨line_smooth P w, fun _=> by simpa only [if_neg hw,if_true] using (hT h h.le_refl).symm,fun i h=>by omega⟩; -- equality use manually
   rw [ ← Nat.cast_sub hw ]; apply sweepOut (line_smooth P w) (gaugeTag w); · exact List.prod_eq_one (fun z hz=> by rcases List.mem_map.mp hz with ⟨k,hk,rfl⟩; exact σ0 k)
   intro i hx; obtain hh:= hT (i+w.length) (by omega); rw [if_pos (by omega), Nat.add_sub_cancel] at hh; rw [hh]; split_ifs <;> first| rfl| omega
lemma realistic {F:Labels.Frame G d}{H:YM.Source.Hol G}(S:YM.Source.SectionData F)(h:S.Sound H)(p:Bid.pop S)(i:F.Index){x:Glow G}(hv:Bank x (bare S i) (F.grades i).2 (Heat.Top.raw (Heat.Top.rendered S p).toData i)): MS.Lifting.Fits x (Theater.orbit G (F.basis i).val) (F.grades i).2 (F.grades i).1 false:= by
   unfold Fits; rw [hv.maskEq]; let T := PertExtension.LatticePT.topMatrix S H h p; let P:= T.basis i
   have hZ := PertExtension.LatticePT.Vertex.basis_fixed S H h p i; have hL:F.coords.symm (T.joint P)= F.basis i:= by rw [T.retr,← F.coords_basis,F.coords.symm_apply_apply]
   have hP := (Heat.HueTag.shadow_eq (F:=F) P hZ); change F.coords.symm (T.joint P)= _ at hP; refine pullJet (d:=d) (F.bound i) (congr_arg Subtype.val (hP.symm.trans hL)) ?_
   intro k hk; obtain he:= pure_grade (F.grades i) (F.basis i) |>.mp (F.pure i) hk; rw [Labels.weight_slot] at he; exact congr_arg Prod.fst he
end cut
end YM.FVA2.Plate
