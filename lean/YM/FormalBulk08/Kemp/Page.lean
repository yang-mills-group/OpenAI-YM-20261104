import YM.FormalBulk08.Kemp.Fan

/-! Studio readout linear in tested profiles, Anthem real formal algebra over P(T).
Power-series coefficients act by convolution in order, not pointwise at any coupled β. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree Wine
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J X: Type*} {η θ A B : ℝ} {l i u j t r D d : ℕ}{K: KernelChoices}{a:Loc G 1}{s: Signed}

-- vector module bookkeeping

def surf (p:Pence)(T:Pot G) : Pot G:=fun e r=>∑ j∈Finset.antidiagonal e, coeff j.1 p • (T j.2 r)
def launch (p:Pence)(Y: Anthem D G): Anthem D G:= fun x=>surf p (Y x)
-- commutative powers cancel via each profile
abbrev wagesP (T:Pot G)(r:ℕ)(u:chain (edgeL G) r):Pence:=PowerSeries.mk fun j=> T j r u
lemma wages_surf (p:Pence)(T:Pot G)(v:chain (edgeL G) r): wagesP (surf p T) r v=p*wagesP T r v:= by ext1 n; simp_rw [wagesP,coeff_mk,coeff_mul,surf,Finset.sum_apply]; simp
lemma wages_ext (T Z:Pot G)(h:∀ r p,wagesP T r p=wagesP Z r p):T=Z := by funext i r p;simpa only [wagesP,coeff_mk] using congr_arg (coeff i) (h r p)
lemma launch_launch (p q:Pence)(Y: Anthem D G):launch p (launch q Y)=launch (p*q) Y:= by funext x; apply wages_ext; intro r a; simp only [launch,wages_surf,mul_assoc]
lemma launch_add (p q:Pence)(Y: Anthem D G): launch (p+q) Y= launch p Y + launch q Y := by funext x e r v; simp [launch,surf,add_smul,Finset.sum_add_distrib]
lemma launch_plus (p:Pence)(X Y: Anthem D G):launch p (X+Y)=launch p X+launch p Y:= by funext x e r v;simp [launch,surf,Finset.sum_add_distrib]
lemma launch_C (c:ℝ)(Y: Anthem D G): launch (C c) Y=c • Y := by
   funext x; apply wages_ext; intro r p; unfold launch; rw [wages_surf]; ext1 n; rw [coeff_C_mul,wagesP,coeff_mk,wagesP,coeff_mk];rfl
lemma launch_one (Y: Anthem D G): launch 1 Y=Y:= by rw [←map_one C,launch_C,one_smul]

variable {Y Z W T:Anthem D G}
lemma Wade.summable (p:Dawn.Studio D) (h:Wade a Y l) (e r): Summable (Y p e r):= by obtain ⟨s,C,hs,-,H⟩:=h.2.2 e r; exact (penn_total (H p) hs.le).of_norm
lemma Wade.through (h:Wade a Y l)(hu:l≤u): Wade a Y u:= by refine ⟨fun p e r he=>?_,h.2⟩; have he:=h.1 p e r he; unfold Yield at *; omega
lemma Wade.add (h: Wade a Y l)(hz: Wade a Z l): Wade a (Y+Z) l:= by
   refine ⟨fun p e r ht=>?_,fun p e r=>(h.2.1 p e r).add (hz.2.1 p e r),fun e r=>?_⟩
   · by_contra he; rw [Pi.add_apply,Pi.add_apply, Pi.add_apply, show Y p e r=0 from Classical.byContradiction fun hv=> he (h.1 p e r hv),show Z p e r=0 from Classical.byContradiction fun hv=> he (hz.1 p e r hv),add_zero] at ht; contradiction
   obtain ⟨s,C,hs,hC,H⟩:=h.2.2 e r; obtain ⟨t,B,ht,hB,E⟩:=hz.2.2 e r; refine ⟨min s t,C+B,lt_min hs ht,add_nonneg hC hB,fun x=>?_⟩; rw [add_mul]; exact (penn_shrink (H x) (min_le_left ..)).add (penn_shrink (E x) (min_le_right ..))
lemma limelight {G: Reach X}{o: X}{T:I→J→Tile X r}{c : J→ℝ} (S:Finset I)(h:∀ i∈S,∃ η:ℝ,0<η ∧ LightPay G η o (T i) c): ∃ η:ℝ,0<η ∧ LightPay G η o (fun x=>∑ i∈S,T i x) c:= by
   have H (i) {s t : ℝ}(v:LightPay G s o (T i) c)(e:t≤s) : LightPay G t o (T i) c:= by obtain ⟨B,h,H⟩:=v; exact ⟨B,h,fun x=>penn_shrink (H x) e⟩
   obtain hh|hh:=S.eq_empty_or_nonempty
   · subst S; simp only [Finset.sum_empty]; exact ⟨1,one_pos,0,le_rfl,fun i=> by rw [zero_mul]; exact Knox_zeros _⟩
   choose! k hv hk using h; obtain ⟨a,ha,hA⟩:= Finset.exists_min_image _ k hh;exact ⟨k a,hv a ha,pay_sums S (fun i hi=>H i (hk i hi) (hA i hi))⟩
lemma Wade.launch (p:Pence)(h:Wade a Y l): Wade a (launch p Y) l:= by
    unfold _root_.YM.FormalBulk08.Kemp.launch surf Wade; refine ⟨fun x e r hx=> ?_,fun x e r=> Agate.sums _ (fun i _=>(h.2.1 _ _ _).smul _),fun e r=>?_⟩
    · by_contra hp; apply hx; refine Finset.sum_eq_zero fun i hi=> ?_; by_cases he:Y x i.2 r=0
      · rw [he,smul_zero]
      have hh:=h.1 x i.2 r he; rw [Finset.mem_antidiagonal] at hi; unfold Yield at *; omega
    let c (x : Dawn.Studio D):=‖x‖
    have hh(i:ℕ×ℕ) : ∃ η:ℝ,0<η ∧ LightPay (fame _) η (0,a) (fun x=> coeff i.1 p • Y x i.2 r) c := by obtain ⟨s,C,hp,hC,H⟩:=h.2.2 i.2 r;exact ⟨s,hp,LightPay.amp (show LightPay _ s _ _ c from ⟨C,hC,H⟩) _⟩
    obtain ⟨η,hs,B,hB,H⟩:=limelight (Finset.antidiagonal e) fun i _=>hh i; exact ⟨η,B,hs,hB,H⟩
lemma Wade.real_scale (b:ℝ)(h:Wade a Y l): Wade a (b • Y) l:=by rw [←launch_C]; exact h.launch _
lemma Wade.neg (h: Wade a Y l): Wade a (-Y) l:= by simpa using h.real_scale (-1)
lemma Wade.sub (h:Wade a Y l)(e:Wade a Z l): Wade a (Y-Z) l:=sub_eq_add_neg Y Z ▸ h.add e.neg
lemma wade_zero : Wade a (0: Anthem D G) l:= by refine ⟨fun p e r (he: (0:Tile _ _ )≠_)=> ?_,fun _ _ _=>agate_zero _,fun e r=> ⟨1,0,one_pos,le_rfl,fun i=>by rw [zero_mul];exact Knox_zeros _⟩⟩; exact False.elim (he rfl)
lemma banner_rise (hy:Wade a Y l)(h:l≤u) (n p): banner l (Y p) n=banner u (Y p) n:= by ext1 e;obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le h; exact sail (Y p) _ (hy.1 p) _ i _
lemma banner_sieve {T:X→Tile (edgeL G) r}(U:Finset X)(h:∀ i∈U,Summable (T i))(m:Side): sieve m (∑ i∈U,T i) =∑ i∈U,sieve m (T i):= by
   induction U using Finset.induction with
   | empty=>simp
   | @insert i Q hi ih=>
      have hh(j)(hj:j∈Q):=h j (Finset.mem_insert_of_mem hj)
      have he : Summable (∑ i∈Q,T i):= by
         have he:=summable_sum hh; simp_rw [←Finset.sum_apply] at he; exact he
      rw [Finset.sum_insert hi,Finset.sum_insert hi,(sieve_sub_add m (h i (Finset.mem_insert_self ..)) he).1, ih hh]
lemma banner_mul (h:Wade a Y l) (p:Dawn.Studio D)(b:Pence)(n: Side): banner l ((launch b Y) p) n= worm (wire G n) b*banner l (Y p) n:= by
    have he:=h.launch b; ext1 j;apply Eq.trans (_ : coeff j _=_) rfl
    let U:=banner l (Y p) n; let S: Pap (wire G n):= worm _ b*U
    have hy i: marble i (coeff j S)=sieve n ((launch b Y) p j i):= by
       unfold S; rw [coeff_mul,←canyon_eq,map_sum]; unfold launch surf
       have hh (x:ℕ × ℕ): Summable (coeff x.1 b • Y p x.2 i):= (h.summable p x.2 i).mul_left (coeff x.1 b)
       rw [banner_sieve (T:=fun x:ℕ × ℕ => coeff x.1 b • Y p x.2 i) (Finset.antidiagonal _) (fun x _=> hh x)]; apply Finset.sum_congr rfl; intro x hx
       rw [show coeff _ (worm _ b)=MvPolynomial.C _ from (show coeff x.1 (worm (wire G n) b)=_ from coeff_map ..),←MvPolynomial.smul_eq_C_mul,map_smul,canyon_eq,sieve_smul,show marble i (coeff _ U)=_ from badge (Y p) (h.1 p) (h.2.1 p) le_rfl n x.2 i]
    calc coeff j (banner _ _ _) = ∑ i∈Finset.range (l+j+1),facade i (sieve n ((launch b Y) p j i)) := coeff_mk _ _
         _ = coeff j S := by
             simp_rw [←hy]; refine crema _ _ ?_; intro r hr; rw [hy, show launch b Y p j r=0 from Classical.byContradiction (fun h=> not_lt.mpr (he.1 _ _ _ h) hr),sieve_zero]
end YM.FormalBulk08.Kemp
