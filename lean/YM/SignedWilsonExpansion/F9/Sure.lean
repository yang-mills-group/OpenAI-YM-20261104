import YM.SignedWilsonExpansion.F9.Solver
/-!
# Ground probe marches in its own engineering units

Boundary requirement for P̂ includes ALL ranks through h. Highest-rank
principal unglazed probe marches *unchanged* when it has weight h; no
same-weight f-mesh Wick subtraction. Lower rank projections need not
be diagonal. Use one pure F axis and retain full lower costs on their
polynomial bill. This also keeps the solution's sign determined.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m c N u e i j l r q:ℕ}{F:Labels.Frame G h}{H:Hol G} {Q:SectionData F}
variable {B M X Y z:ℝ}{P:SourceP F}{U:Type*}[Fintype U]{E W:Credit}{R:Realm G (q+1) E}

def pureF (F:Frame G h)(i:F.Index)(q:ℕ): BankP F q := Pi.single (i,0) 1
lemma own (F:Frame G h)(i:F.Index)(q:ℕ)(j:F.Index) : pureF F i q (j,0)= if i=j then 1 else 0:=by by_cases p:i=j <;> simp [pureF,p,Ne.symm]
/-- Ground bound initially through earlier slot ranks. -/
def loftP (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(i:F.Index): BankP F q:= solve p v 0 (pureF F i q)
def loft (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(i:F.Index): Era G ℝ:= rack F P (loftP p v i)
lemma loft_target (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(i:F.Index): heard F A Ñ k N q c m (loft p v i)=pureF F i q:=by
    simpa only [zero_add, loft, loftP] using solve_target p v (pureF F i q) (silent G k)
lemma loft_allow (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(i:F.Index):
    let a:= (Enough F q u k).buy X; (∀ j, ‖loftP p v i j‖ ≤ a) ∧ ∀ l,m≤ l→l≤c→ ∀ e≤q,∀ r,Fruit 0 1 u ((pier A Ñ N h k c l (loft p v i)).2 e r) a:=by
    intro a; simpa only [mul_one,zero_add, loft,loftP] using solve_bounds p v (pureF F i q) (silent G k) zero_le_one (fun _ _ _=> Fruit.zero.more zero_le_one) (fun j=>by by_cases h : j=(i,0) <;> simp [pureF,h])
lemma loft_upper (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X) (i:F.Index)(g:wr F i<r) :
    let P':=loft p v i; (∀ l,m≤ l→l≤c→(pier A Ñ N h k c l P').2 0 r=0) ∧ ∀ j:TagIx F r, loftP p v i (eyeTag F 0 q (Nat.zero_le _) j)=0:=by
    intro P'; let x:=loftP p v i; have he (e j:ℕ)(w:When e j 0 r):Fruit 0 1 u (((0:Era G ℝ).2) e j) 0:= Fruit.zero
    have hp(e j)(h0:When e j 0 r)(i':TagIx F j): ‖row F ((pier A Ñ N h k c m ((0:Era G ℝ)+rack F P x)).2 e j) i'‖ ≤ 0:= by
       unfold When at h0; have ht:e=0:=by omega
       rw [zero_add, ht,output_at _ (Nat.zero_le q), show rack F P x=loft p v i from rfl,show output F _ (pier _ _ _ _ _ _ _ _) = _ from loft_target p v i, show eyeTag F 0 q _ i'=(i'.val,0) from rfl, own F i, if_neg (show i≠ i'.val from ?_), norm_zero]
       intro hx; have hg:wr F i=j:=by rw [hx]; exact i'.property
       omega
    obtain ⟨D,H⟩:= billed F q u k
    obtain ⟨h1,h2⟩:= H 0 (Nat.zero_le _) r Q A Ñ m c N 0 X P 0 x 0 r (Nat.zero_le _) (Or.inr ⟨rfl,le_rfl⟩) le_rfl p (silent G k) v he hp; simp_rw [mul_zero,zero_add] at h1; refine ⟨fun i hi hx=>fruit_nil (h1 i hi hx),fun j=>?_⟩; apply norm_le_zero_iff.mp; exact ((h2 (Nat.zero_le _) j).trans_eq (mul_zero _)) -- trans_eq

lemma Down.inject {t:U→ℕ}{Z:Matrix U U ℝ}(p:Down t Z X)(hp:0≤X)(h:ℕ)(hk:∀ i,t i≤h): Injective (Z *ᵥ ·):=by
    intro a b x; let T:=a-b; obtain ⟨D,H⟩:= oneRow t (h+1) (fun i=> Nat.lt_succ_of_le (hk i)) Credit.unit (pur X)
    have hb:Down t Z ((pur X).buy 1):=⟨p.self,fun i j=>(p.value i j).trans (pure_goal ..),p.ties⟩
    have ht: Z *ᵥ T=0:= by unfold T; change Z*ᵥa=Z*ᵥb at x; rw [mulVec_sub,x,sub_self];
    have he(i:U): T i=0:=norm_le_zero_iff.mp ((H 1 le_rfl 0 le_rfl Z T hb (fun i=>by rw [ht,mul_zero,Pi.zero_apply,norm_zero]) i).trans_eq (mul_zero _)); exact sub_eq_zero.mp (funext he)
lemma summit (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(i:TagIx F r)(g:wT F i=h):
    ∀ l,m≤ l→ l≤c → row F ((pier A Ñ N h k c l (loft p v i.val)).2 0 r)=Pi.single i 1:=by
    have h0(c':ℕ)(b:m≤ c')(d:c'<c):= v.pays c' 0 r b d (Nat.zero_le _) ((fitsRank F i).trans (v.order.trans (Nat.le_add_right ..)))
    intro l hh0 hp; induction hh0 with
    | refl=>
        funext j; rw [output_at _ (Nat.zero_le q),show output F _ (pier _ _ _ _ _ _ _ _)=_ from loft_target p v _, show eyeTag F 0 q _ j=(j.val,0) from rfl, own]; by_cases H:i=j
        · rw [H,if_pos rfl,Pi.single_eq_same]
        rw [if_neg (fun v=>H (Subtype.ext v)), Pi.single_eq_of_ne (Ne.symm H)]
    | @step l hL ih=>
       have he :m≤ l:=hL
       let P':=loft p v i; let T j:=pier A Ñ N h k c j P'; let R:= stepT Q A Ñ l k N r; have H :Earlier (T (l+1)) 0 r u 0:=by
           intro i' j h; rcases h with e|⟨a,b⟩; exact False.elim (Nat.not_lt_zero i' e); subst i'; rw [show (T _).2 0 _=_ from (loft_upper p v i.val (lt_of_le_of_lt (show wr F i.val≤r from i.property.le) b)).1 (l+1) (by omega) hp]; exact Fruit.zero
       have hf:= h0 l he hp; let C:= T (l+1); have hu: Auth k P':= p.mix _; have hx:Auth k C:=piered v.simple v.ratios hp v.cap hu
       obtain ⟨a,hA⟩:= attends hx 0 r u
       have hh := (hf.back C 0 a hx le_rfl H hA).1
       apply ((staff hf).inject (zero_le_one.trans v.pos) _ (fun i=> F.bound _))
       funext j; have hr: (R *ᵥ row F (C.2 0 r)) j= row F ((T l).2 0 r) j:= by rw [show T l=pointStep _ _ _ _ _ _ C from pier_step v.simple v.ratios hp v.cap hu]; exact Eq.symm (sub_eq_zero.mp (norm_le_zero_iff.mp ((hh j).trans_eq (mul_zero _))))
       specialize ih (by omega); change (R*ᵥ _) j=(R *ᵥ_) j; rw [hr, show row F ((T l).2 0 r)=Pi.single i 1 from ih,Matrix.mulVec_single_one R i];
       change _=stepT Q A Ñ l k N r j i
       rw [hf.top j i (by rw [g]; exact F.bound _)]; by_cases h:j=i
       · subst j; rw [if_pos rfl,Pi.single_eq_same,g]; simp
       rw [if_neg h,Pi.single_eq_of_ne h]
lemma tie (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(i:TagIx F r)(g:wT F i=h): paper (r:=r) (loftP p v i.val) 0 (Nat.zero_le q)= Pi.single i 1:=by
    let L:= loftP p v i.val; let V:=loft p v i.val; let Q':= typus F P r; let D:= rowCost F u r * X
    have hp:= p.licensed (v.ample.more ((fitsRank F i).trans (v.order.trans (Nat.le_add_right ..))))
    apply hp.inject (mul_nonneg (rowCost_nn F) (zero_le_one.trans v.pos)) h (fun i=> F.bound _)
    have ht: before F P L 0 r=0:=by
       unfold before; refine Finset.sum_eq_zero (fun j hj=>?_); let a:= j.1; have H:= (Finset.mem_filter.mp hj).2
       have he : j.2.val=0 ∧ r< wr F a:= by unfold lowerGrade at H; unfold a; omega
       rw [show L j=0 from ?_, zero_smul]
       have hv: j=eyeTag F 0 q (Nat.zero_le _) (⟨a,rfl⟩:TagIx F (wr F a)):= Prod.ext rfl (Fin.ext he.1)
       rw [hv]; exact (loft_upper p v i.val (lt_of_le_of_lt (show wr F i.val≤ r from i.property.le) he.2)).2 _
    have hz:=summit p v i g c v.length le_rfl; rw [pier_top] at hz; funext j; change (typus F P r *ᵥ paper L 0 _) j=(Q' *ᵥ Pi.single i (1:ℝ)) j; rw [← p.price L,Matrix.mulVec_single_one]
    rw [show (sliceP F P L 0 r _).2 0 r=(loft p v i.val).2 0 r from ?_,hz]; swap
    · unfold loft; rw [p.slim,ht,show (_:Era G ℝ).2 0 r= _ from (show (0:Era G ℝ).2 0 r=0 from rfl),zero_add]
    change Pi.single (M:=fun _ : TagIx F r=>ℝ) i (1:ℝ) j=Q' j i
    have hh :Q' j i= _:= p.high r j i (show wT F j≤wT F i from g.symm ▸ F.bound _); rw [hh]; by_cases h:j=i
    · subst j; rw [if_pos rfl,Pi.single_eq_same]
    rw [if_neg h, Pi.single_eq_of_ne h]
end YM.WilsonCoeffUV.Mer.Xa
