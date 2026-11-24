import YM.Contacts.Milling.Kite
import YM.AnalyticNext.QUARTIC_MATCH.Multiples
/-! Jet conservation on arbitrary tori via test pull-ups. Station law R not
    sampled on the smaller period; projectors at THAT period keep their embedded lives. -/
noncomputable section
namespace YM.Contacts.Milling.Convoy
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open AnalyticNext.QuarticMatch.Sheets Kale Ion Steam
open scoped Topology BigOperators Classical Matrix NNReal ContDiff
variable {α W X Y Z ι:Type}{b:ℝ}{l:Range Z}{z:X→Y}{p:Z→ X}{k:ℕ}
-- composition with second projected roll itself covering
variable {F:Field ι X}{G:Field ι Y}{K:Field ι Z}
lemma gap_cut [Fintype ι](h1:Shadow p K F)(h2:Shadow (z∘p) K G) (hp:Surjective p)(hP:Rooted l K b): Shadow z F G:= by
   intro i x t; obtain ⟨a,rfl⟩:= hp x; let w: Locked X i (p a)→ℝ:= fun u=> F u.val; let q:= roll p i a; let k:=roll z i (p a); have hh : Scroll k w (cram k w):= fun b=> rfl; exact (h2 i a t).trans ((Scroll.comp (h1 i a) hh ((hP.raw i a).2.1.of_norm) t).symm)
local notation "τ" => (𝓝 (0:ℝ))
variable [Fintype ι][Fintype X][Fintype Y]
private lemma qsum {f:X→ℝ}{g:Y→ℝ}(h:Scroll z f g): ∑ x:X,f x=∑ y:Y,g y:= by have he:= (heavy z (show Summable f from .of_finite)).tsum_eq; simp_rw [tsum_fintype,←funext h] at he; exact he.symm
private def orient (i:ι) : ( (a:X)×Locked X i a)≃(ι→X):= ⟨fun z=> z.2.val,fun u=> ⟨u i,⟨u,rfl⟩⟩,fun ⟨a,u,H⟩=> by subst a; rfl, fun _=>rfl⟩
lemma kernelcrew {v:House.Dir Y}(h:Shadow z F G)(i:ι) (t:ℝ) (hh : ∀ f:Y→ℝ, ∑ x:X,f (z x)= t * ∑ i,f i): design F (v∘z)= t*design G v:= by
   let W (x:X): Fintype (Locked X i x):= by unfold Locked; infer_instance; -- no?
   let g (i:ι→Y) := ∏ j,v (i j); let V (b:Y):= ∑ q:Locked Y i b,g q.val* G q.val; let H (u:ι→X):=∏ i,v (z (u i)); have he (b:X): ∑ q: Locked X i b,g (z∘q.val)*F q.val= V (z b):= qsum (show Scroll (roll z i b) _ _ from (h i b).filter (t:=fun p: Locked Y i (z b)=> g p.val))
   rw [design_spec,design_spec,←Equiv.sum_comp (orient (X:=X) i),← Equiv.sum_comp (orient (X:=Y) i),Fintype.sum_sigma,Fintype.sum_sigma]; simp_rw [mul_comm (F _),mul_comm (G _)]; change (∑ b:X,∑ q:Locked X i b,g (z∘q.val)*F q.val)= t * ∑ b:Y,V b; simp_rw [he]; exact hh V
variable {m n:Side}
-- soar/zip
variable (h:m.val∣ n.val)
def spool (x:Co n α):Co m α:=(AnalyticNext.QuarticMatch.Sheets.project h x.1, x.2)
lemma lowers_spool : spool h ∘ lower n= lower (α:=α) m:= funext fun x=> Prod.ext (project_wrap h _) rfl
lemma boards [Fintype α](u:Co m α→ℝ) : ∑ x:Co n α,u (spool h x)=(mult h:ℝ)*∑ i:Co m α,u i:= (count_extra h u).trans (nsmul_eq_mul ..)
def still [Fintype α] : House.Dir (Co m α) →L[ℝ] House.Dir (Co n α):= ContinuousLinearMap.pi fun x=> ContinuousLinearMap.proj (spool h x)
def loom (α:Type): Matrix (Co n α) (Co m α) ℝ := (FreeResolvent.insertion (spool (α:=α) h))ᵀ
lemma steer_loom [Fintype α](x:House.Dir (Co m α)): loom h α *ᵥ x=still h x:= by funext y; simp [loom, Matrix.mulVec,dotProduct,FreeResolvent.insertion]; rfl
lemma mult_upper : 0<(mult h:ℝ):= by exact_mod_cast mult_pos h
abbrev whip [Fintype α](P: House (Co n α)): House (Co m α) := fun i j=> (mult h:ℝ)⁻¹ • hoist (loom h α) (P i j)
lemma loom_pay [Fintype α]: Weirs (fun _ _=>1) (loom h α) (mult h:ℝ) 1:= by
   have hp:= mult_upper h; refine ⟨hp.le,zero_le_one,fun y=>?_ , fun x=>?_⟩
   · apply budget_finite (fun x=>by positivity); simp only [loom,Matrix.transpose_apply,FreeResolvent.insertion,Matrix.of_apply,apply_ite (fun x:ℝ=>‖x‖),norm_one,norm_zero,mul_one]; erw [show (∑ i:Co n α, if spool h i=y then (1:ℝ) else 0)=_ from boards h (fun i=>if i=y then 1 else 0)]; simp
   apply budget_finite (fun x=>by positivity); simp [loom,Matrix.transpose_apply,FreeResolvent.insertion,apply_ite (fun x:ℝ=>‖x‖)]
lemma penn [Fintype α](x:House.Dir (Co m α))(P: House (Node α)) (hP: Cradle α P){s:ℝ≥0}{B:TableFee}(hp:Roof s P B) (i r:ℕ)(hv:r≠0): design (hair P n i r) (still h x)=(mult h:ℝ)*design (hair P m i r) x:= by
   let V:= spool (α:=α) h; have ht := lowers_spool h (α:=α); let W(y :Side):= hair P y i r; have he y: Shadow (lower y) (P i r) (W y):=printFeeds (heritage (fun p=>hP.here p i r) y); exact kernelcrew (v:=x) (gap_cut (he n) (by rw [ht]; exact he m) (lower_onto n) (hp.shelter i r)) (⟨0,Nat.pos_of_ne_zero hv⟩:Fin r) _ (boards h)

lemma design_scale (a:ℝ)(F:Field ι X)(x:House.Dir X): design (a • F) x=a*design F x:= by simp only [design,verse_scale', map_smul, smul_eq_mul]
lemma whip_beam [Fintype α](i j:ℕ)(P:House (Co n α)) : (design (whip h P i j))=(mult h:ℝ)⁻¹ • ( design (P i j) ∘ still h):= by ext1 x; rw [whip, Convoy.design_scale, hoist_read,steer_loom]; rfl
lemma whip_ward [Fintype α](i j:ℕ)(P:House (Co n α)) : wind (whip h P) k i=(mult h:ℝ)⁻¹ • (wind P k i ∘ still h):= by
  ext x; simp only [wind,Function.comp_apply,Pi.smul_apply,smul_eq_mul,mul_sum]; apply sum_congr rfl; intro i _; unfold grate; split; rw [whip_beam]; rfl; simp
lemma parcel_sub (F Q:Pulse.Field ι X)(x:House.Dir X):design (F-Q) x=design F x-design Q x:= by simp only [design_spec,Pi.sub_apply,Finset.sum_sub_distrib,sub_mul,Finset.sum_sub_distrib]
lemma wind_minus {α:Type}[Fintype α](i j:ℕ)(P U:House α) : wind (P-U) k i=wind P k i- wind U k i:= by
   ext x; simp only [wind,Pi.sub_apply,←Finset.sum_sub_distrib]; apply sum_congr rfl; intro j h; unfold grate; split <;> first| exact parcel_sub _ _ x| simp
lemma split_zero {P: House X}(i j:ℕ)(x:House.Dir X) : wind P j i x-wind P j i 0=wind (kiss P) j i x:= by
  simp only [wind,← Finset.sum_sub_distrib]; refine sum_congr rfl fun r _ => ?_; unfold grate; split
  next e=> change _-_=design (if r=0 then 0 else _) x; split
           next h=> subst r; have he (P:House X)(i:ℕ): design (P i 0) x=design (P i 0) 0:= by simp [design_spec]
                    rw [he,sub_self,parcel_nil]
           next h=> have hv:= House.design_scale P i r x 0; rw [grate,if_pos e,zero_smul,zero_pow h,zero_mul] at hv; rw [hv,sub_zero]
  simp
variable {J D:TableFee}{G: YM.Gauge}{Y:House (Co m α)}{P:House (Co n α)} [Fintype α]
lemma scaled_bound {i j:ℕ}(B:ℝ)(hp:Rooted (Range.cheap _) (P i j) B): Rooted (Range.cheap (Co m α)) (whip h P i j) B:= by
   apply Rooted.weaken (Rooted.smul (hoist_pay flat_ripple (loom_pay (α:=α) h) hp) (mult h:ℝ)⁻¹) (fun _=>le_rfl) ?_; have hp:= mult_upper h; simp [mul_inv_cancel, hp.ne']
lemma zero_not_paid (P:House (Node α))(hP:Cradle α P)(n:Side)(i:ℕ): hair P n i 0=0:= by rw [hair,hP.scalar,printLull]
-- Convergent whipped differences
variable {A D : Type}
lemma jet_empty (j:ℕ) {E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E] (x:E): jet (fun _:E=> (0:ℝ)) j x=0:= by cases j; rw [jet_zero]; unfold jet; rw [iteratedFDeriv_const_of_ne (by omega)]; simp
-- tendsto termwise jet at fixed u small torus. Assume pointwise. variation by move-germ of x fixed.

lemma design_tend (p: Filter A){E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](j:ℕ)(x:E)(Tq:E→House.Dir X)(ht : AnalyticAt ℝ Tq 0) {Q:A→Field ι X} (hq:∀ i,Tendsto (fun a=> Q a i) p (𝓝 0)): Tendsto (fun a=> jet (design (Q a)∘ Tq) j x) p (𝓝 0):= by
   let g (i:ι→X)(x:E):= ∏ k,Tq x (i k); have hg i : AnalyticAt ℝ (g i) 0:= by unfold g; exact (contDiffAt_prod (fun j _=> (ContinuousLinearMap.contDiff (show House.Dir X →L[ℝ] ℝ from ContinuousLinearMap.proj (i j))).contDiffAt.comp (f:=Tq) _ ht.contDiffAt)).analyticAt -- field names
   have he a: jet (design (Q a) ∘ Tq) j x=∑ i:ι→X, Q a i*jet (g i) j x:= by
      rw [show design (Q a) ∘ Tq=(fun x=>∑ i:(ι→X), Q a i*g i x) from (by ext1 x; exact design_spec (Q a) (Tq x)),loan_sum _ (fun i _=> ContDiffAt.analyticAt (contDiffAt_const.mul (hg i).contDiffAt))]; apply sum_congr rfl; intro i _; unfold jet; rw [show (fun x=> Q a i*g i x)=_ from (show (fun x=> Q a i*g i x)=(Q a i • g i) from rfl), iteratedFDeriv_const_smul_apply (hg i).contDiffAt]; change _*(_* (_:ℝ)) = _; ring_nf; rfl
   simp_rw [he]; simpa using (tendsto_finsetSum Finset.univ (f:=fun j a=>Q a j*jet (g j) _ x) (fun i _=>(hq i).mul_const (jet (g i) j x)))
lemma viva [Nonempty A] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (l: Filter A)(i j:ℕ)(x:E)(Tq:E→House.Dir (Co m α))(ht:AnalyticAt ℝ Tq 0)(X: A→House (Co m α))(h:∀ r i p,Tendsto (fun j=> X j i r p) l (𝓝 0)) : Tendsto (fun a=> jet (wind (X a) k i ∘ Tq) j x) l (𝓝 0):= by
   let g (a:A)(c:ℕ):= grate (X a) i c ∘ Tq; have he a: jet (wind (X a) k i ∘ Tq) j x=∑ b∈ Finset.range (k-i),jet (g a b) j x:= loan_sum (Finset.range (k-i)) (fun b _=> (grate_ana (X a) i b _).comp ht) j x
   have hd b:Tendsto (fun a=> jet (g a b) j x) l (𝓝 0):= by
      by_cases hu:2 ≤ i + b
      · have hf a: g a b=design (X a (i+b-2) b)∘ Tq:= by unfold g grate; simp only [if_pos hu]
        simp_rw [hf]; exact design_tend _ _ x _ ht (Q:=fun a=> X a (i+b-2) b) (h b _)
      have he a:g a b=(fun _: E=>0):= by ext1 x; simp [g,grate,hu];
      simp_rw [he,jet_empty]; exact tendsto_const_nhds
   simp_rw [he]; simpa using tendsto_finsetSum (Finset.range (k-i)) (fun i _=> hd i)
lemma penn_jet (u:House.Dir (Co m α))(F:House (Node α)){s:ℝ≥0}{B:TableFee} (hF: Cradle α F)(hp:Roof s F B) (i j:ℕ) : wind (hair F n) k i (still h u)=(mult h:ℝ)*wind (hair F m) k i u:= by
    unfold wind; rw [mul_sum]; apply sum_congr rfl; intro j hj; unfold grate; split
    next he=> by_cases h:j=0; subst j; simp_rw [zero_not_paid F hF, design]; simp; exact penn _ _ _ hF hp _ _ h
    simp
open Stationary
variable {Γ: Gauge}
lemma still_stain (u:Γ.El)(x:Link Γ m): still h (stain u x)= stain u (still h x):= rfl
lemma still_spin (s:Signed)(x:Link Γ m): still h (orderTurn s x)=orderTurn s (still h x):= by
    ext1 ⟨i,a,b⟩; obtain ⟨t,rfl⟩:= axisEquiv.surjective a; change flipCoords s ℝ x (AnalyticNext.QuarticMatch.Sheets.project h i,coord t,b)= flipCoords s ℝ (x ∘ spool h) (i,coord t,b); rw [flip_price,flip_price]; split <;> simp [← project_signed h,map_sub, project_step,spool]
def rise (Γ:Gauge): Swatch Γ m →L[ℝ] Swatch Γ n:= (still h).prodMap (still h)
lemma still_move (x:Swatch Γ m): still h (moveField x)=moveField (rise h Γ x) := by
    unfold moveField; have he : shiftLinks (rise h Γ x)=copies h (shiftLinks x) := (gauge_copies h (input Γ m x.2) (switchSite x.1))
    rw [he]; rfl
lemma whipping (P: House (Lines Γ n 1))(hp:sealed P k) : sealed (whip h (kiss P)) k := by
    intro i hi; let Y:=whip h (kiss P); let W:=wind Y k i; let c:ℝ:=(mult h:ℝ)⁻¹; let V:=wind P k i; have he x : W x= c * (V (still h x)-V 0):= by unfold W; rw [show wind Y k i=_ from whip_ward h i 0 (kiss P), Pi.smul_apply,Function.comp_apply,←split_zero]; rfl
    have hg:= hp i hi; refine ⟨continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt), wind_ana ..,fun u x=>?_,fun s x=>?_,?_⟩
    · change W _=W x; rw [he,he,still_stain h,show V (stain _ _)=_ from hg.color _ _]
    · change W _=W x; rw [he,he,still_spin h,show V (orderTurn _ _)=_ from hg.spins _ _]
    let T:= V ∘ moveField; let A:Swatch Γ n→ℝ:= V ∘ Prod.snd; have hl: AnalyticAt ℝ A 0 := (hg.analytic).comp (f:= Prod.snd) contDiffAt_snd.analyticAt; have hu:AnalyticAt ℝ T 0 := AnalyticAt.comp (f:= moveField) (g:=V) (moveField_zero (G:=Γ) (m:=n)|>.symm ▸ hg.analytic) moveField_analytic
    change Rays _ (fun z:Swatch Γ m=> W _-W _); rw [show (fun z:Swatch Γ m=> W (moveField z)-W z.2)= (fun z=> c*((T-A) (rise h Γ z))) from funext fun z=> by rw [he,he, still_move h]; change _= _ *(V _- V (still h z.2)); ring]; exact fun x=> (merkin (hu.sub hl) hg.grade _ ((rise h Γ).analyticAt _) (map_zero _) x).const_mul_left _
lemma vow_penn {F:House (Node α)}{P:House (Co n α)} {s:ℝ≥0}{B:TableFee}(hF: Cradle α F)(hp:Roof s F B)(i:ℕ): wind (whip h (kiss P-hair F n)) k i = wind (whip h (kiss P)) k i-wind (hair F m) k i:= by
   ext x; rw [whip_ward h i i,wind_minus i i,Pi.sub_apply,whip_ward h i i]; simp only [Pi.smul_apply,Function.comp_apply,Pi.sub_apply,smul_eq_mul,penn_jet h _ _ hF hp i i, mul_sub, inv_mul_cancel_left₀ (mult_upper h).ne']
lemma salve [Nonempty A] {l:Filter A}[l.NeBot]{F:House (Lines Γ m 1)}{P Q:A→House (Lines Γ m 1)} (ht:∀ i r v,Tendsto (fun a=> Q a i r v) l (𝓝 0)) (hp:∀ᶠ a in l,sealed (P a) k)(he: ∀ a i,wind (P a) k i-wind F k i=wind (Q a) k i): sealed F k:= by
   intro i hi; let f:= wind F k i; let p a:=wind (P a) k i; let q a:=wind (Q a) k i
   have hv {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Tq:E→ Link Γ m)(hT:AnalyticAt ℝ Tq 0)(x:E)(j:ℕ) : Tendsto (fun a=> jet (p a∘ Tq) j x) l (𝓝 (jet (f∘Tq) j x)) := by
      have hl:= viva (k:=k) l (α:=Loc Γ 1) i j x Tq hT Q (fun r i=> ht i r); have he a : jet (p a ∘ Tq) j x= jet (q a∘ Tq) j x+jet (f∘ Tq) j x:= by rw [show p a=q a+f from sub_eq_iff_eq_add.mp (he a i),show (q a+f) ∘ Tq=q a ∘ Tq+f∘Tq from rfl,serif (AnalyticAt.comp (g:=q a) (f:=Tq) (wind_ana ..) hT) (f ∘ Tq) (AnalyticAt.comp (g:=f) (f:=Tq) (wind_ana ..) hT)];
      simp_rw [he]; simpa using hl.add_const (jet (f∘Tq) j x)
   have hx (L: Link Γ m →L[ℝ] Link Γ m) (h:∀ᶠ a in l, p a ∘ (⇑L)=p a): f ∘ (⇑L)=f:= by
      let T:= L; refine instant (repeater (wind_controls ..) L) (wind_controls ..) (valued (k-i) (starts _ (wind_ana ..) _) (wind_ana ..) (fun x j hj=>?_)); exact tendsto_nhds_unique (hv _ (L.analyticAt _) x j) (show Tendsto _ _ _ from (hv _ analyticAt_id (x:Link Γ m) j).congr' (h.mono fun a ha=> by dsimp only; rw [ha]; rfl)) -- inference
   refine ⟨continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt),wind_ana ..,fun u=>congr_fun (hx (stain u) (hp.mono fun a ha=> funext ((ha i hi).color u))),fun s=>congr_fun (hx (orderTurn s) (hp.mono fun a ha=> funext ((ha i hi).spins s))),?_⟩
   let P:=moveField (G:=Γ) (m:=m); let g:= (ContinuousLinearMap.snd ℝ (BaseSites Γ m) (Link Γ m)); have hl (f:Link Γ m→ℝ)(hf:AnalyticAt ℝ f 0): AnalyticAt ℝ (f∘ P) 0:=AnalyticAt.comp (by unfold P; rw [moveField_zero]; exact hf) moveField_analytic
   refine (show Rays (k-i) (f∘ P-f∘ g) from valued (k-i) (hl _ (wind_ana ..)) (starts _ (wind_ana ..) _) (fun x j hj=>?_)); exact tendsto_nhds_unique (hv _ moveField_analytic x j) ((hv _ (g.analyticAt _) x j).congr' (hp.mono fun a ha=> by have HE:= ha i hi; exact nightwalk (hl (p a) HE.analytic) (starts (p a) HE.analytic g) HE.grade j hj x|>.symm))
variable {B Fee: TableFee} {M:ℕ→Side}{s:ℝ≥0}
lemma meterwise {B:House (Node α)} (hm:∀ i,m.val∣ (M i).val) (g:ℕ→ℝ) (hg:Tendsto g atTop τ) {P:∀ i,House (Co (M i) α)} (hB: Cradle α B) (he:∀ (i r:ℕ),r≠0 → ∀ᶠ j in atTop, Rooted (Range.cheap (Co (M j) α)) (P j i r-hair B (M j) i r) (g j*Fee i r)) : let X j:= whip (hm j) (kiss (P j)-hair B (M j)); ∀ i r p,Tendsto (fun j=> X j i r p) atTop τ := by
    intro X i r p; by_cases hz:r=0
    · subst r; apply EventuallyEq.tendsto; apply Eventually.of_forall; intro i; unfold X whip; simp only [Pi.sub_apply,kiss,hB.scalar, hair,↓reduceIte,printLull, sub_self, hoist_empty,smul_zero]; rfl
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ((he i r hz).mono fun j hj=>?_ ) (g:=fun j=> g j*Fee i r) (by simpa using hg.mul_const (Fee i r)); apply (scaled_bound (hm j) (P:=kiss (P j)-hair B (M j)) _ ?_).bound p ⟨0,Nat.pos_of_ne_zero hz⟩; simp only [Pi.sub_apply,kiss,if_neg hz]; exact hj
lemma saved (hm:∀ i,m.val∣ (M i).val) {P:∀ i,House (Co (M i) (Loc Γ 1))}{X:House (Node (Loc Γ 1))} (hX: Cradle _ X) (ht:Roof s X B)(g:ℕ→ℝ)(hg:Tendsto g atTop τ)
    (he:∀ (i r:ℕ),r≠0 → ∀ᶠ j in atTop, Rooted (Range.cheap (Co (M j) (Loc Γ 1))) (P j i r-hair X (M j) i r) (g j*Fee i r)) (hv:∀ᶠ j in atTop,sealed (P j) k) : sealed (hair X m) k:= salve (meterwise hm g hg hX he) (hv.mono fun j hj=> whipping (hm j) (P j) hj) (fun a i=> Eq.symm (vow_penn (hm a) hX ht i))
end YM.Contacts.Milling.Convoy
