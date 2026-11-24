import YM.SchemeConversionRG11.FirstW.Invoice.Crown
/-! Exact first separated-orbital row price (in fact arbitrary positions here). Branch deletions before counterterm decomposition. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {r d : ℕ} (o : Full.Grid n r) (h : ℝ)
section dry
variable (x : Orb.Coords G n)
def crestF (z : Who G d) (i : Fin r) := echoLeg h (o i) z.val (spanT x) (spanT x)
def payM (i : Fin r) (t : Full.Aux G d) (q : Part G d) := Full.pairEval h (o i) x t (uncap q)
lemma expense (i : Fin r) (t : Full.Aux G d) (q : Part G d) : First.first (payM o h x i t q)= ∑ z:Who G d,(crestF o h x z i:ℝ)*PowerSeries.constantCoeff (payM o h x i t (MvPolynomial.pderiv z q)) := by
  let F:= payM o h x i t; have e (p q:Part G d): F (p+q)=F p+F q := by simp [F,payM,Full.pairEval,uncap];
  have m (p q:Part G d): F (p*q)= F p * F q:= by simp [F,payM,Full.pairEval,uncap]
  change First.first (F q)=∑ z:Who G d,(↑(crestF o h x z i):ℂ)*PowerSeries.constantCoeff (F (MvPolynomial.pderiv z q))
  induction q using MvPolynomial.induction_on with
  | C c=> simp [F,payM,Full.pairEval,uncap,First.first]
  | add p q j k=> rw [e]; change PowerSeries.coeff (R:=ℂ) 1 _=_; rw [map_add]; change First.first _+First.first _=_; rw [j,k]; simp only [map_add, e,mul_add,Finset.sum_add_distrib]
  | mul_X p z ih=>
    have hp : First.first (F (MvPolynomial.X z))= (crestF o h x z i:ℝ) := by
      unfold First.first F payM uncap Full.pairEval; rw [MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X',map_add,PowerSeries.coeff_C, if_neg (by decide),add_zero]; unfold crestF spanT; exact echo_actual z.val (o i) h x
    let V (u:Who G d):=MvPolynomial.pderiv u p
    let a(u:Who G d):=MvPolynomial.pderiv u (MvPolynomial.X z:Part G d)
    rw [m];change PowerSeries.coeff _ (_*_)=_; rw [PowerSeries.coeff_one_mul];change First.first (F p)*PowerSeries.constantCoeff _ + First.first _ *PowerSeries.constantCoeff _ = _; rw [hp,ih]
    have hg u : MvPolynomial.pderiv u (p * MvPolynomial.X z) = V u* MvPolynomial.X z+p*a u := by simp only [Derivation.leibniz,V,a]; change p * _+ _ * _= _;ring
    let H (u : Who G d) := (↑(crestF o h x u i):ℂ) * (PowerSeries.constantCoeff (F (p*a u)))
    simp_rw [hg,e,map_add,mul_add,Finset.sum_add_distrib,m (V _) (MvPolynomial.X z),map_mul, Finset.sum_mul,mul_assoc]; congr 1
    change _=∑ u,H u; rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ z)]; unfold H a; simp; intro u _ hu; simp [H,a,F,payM, Ne.symm hu,uncap,Full.pairEval]
lemma postW (j : Fin r) (p : Players G r d) : First.dry o h (fun _=>d) (uncap ∘ p) x j=∑ z:Who G d,(crestF o h x z j:ℝ)*PowerSeries.constantCoeff (Full.column d h (o j) (uncap (MvPolynomial.pderiv z (p j))) x) := by
  unfold First.dry First.first; simp_rw [Full.auxiliary, Full.avg,←PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff]; change (∫ u:Full.Aux G d,First.first (payM o h x j u (p j)) ∂Full.auxLaw ..)=_; simp_rw [expense]; rw [integral_finsetSum]; simp only [integral_const_mul]; rfl
  intro i _; apply Integrable.const_mul
  have e:=Full.bareTame_integrable (G:=G) (d:=d) h (Full.leg_ready h (o j) x (uncap (MvPolynomial.pderiv i (p j))) 0)
  simpa only [payM,PowerSeries.coeff_zero_eq_constantCoeff] using e
lemma dayW (i : Fin r) (p : Players G r d) : First.varied Finset.univ o h (fun _=>d) (uncap ∘ p) x i=∑ z:Who G d,(crestF o h x z i:ℝ)*First.line Finset.univ o h (fun _=>d) (uncap ∘ dict (i,z) p) x := by
  rw [First.varied,postW,Finset.sum_mul]; apply Finset.sum_congr rfl; intro z _; rw [mul_assoc]; apply congrArg _; unfold First.line
  rw [←Finset.mul_prod_erase (s:=Finset.univ) (a:=i) (f:=fun t=>First.tube o h (fun _=>d) (uncap ∘ dict (i,z) p) x t) (Finset.mem_univ _)]
  apply congrArg₂ (· * ·)
  · simp only [First.tube,First.lead,comp_def,dict,update_self]
  refine Finset.prod_congr rfl fun k hk=>?_ ; unfold First.tube; simp only [dict,comp_def,update_of_ne (Finset.ne_of_mem_erase hk)]
end dry
variable (p : Players G r d)
def renda := (PowerSeries.coeff 1) (recipe d h o (uncap ∘ p))
def changeR (t x y : At G r d) := (↑(echoLeg h (o t.1) t.2.val (cloudK h o x) (cloudK h o y)):ℂ)*ZeroR o h (dict y (dict x (dict t p)))
def verbR (x y z:At G r d) := (↑((1/2:ℝ)*wheels (fun v w=> tower G v w (cloudK h o x) (cloudK h o y) (cloudK h o z))):ℂ)*ZeroR o h (dict z (dict y (dict x p)))
lemma echo_tame (z:Who G d) (j : Fin r) : Orb.Tame (fun x:Orb.Coords G n=> (↑(crestF o h x z j):ℂ)) := by simp_rw [crestF,spanT, ←echo_actual, Bare.seriesLex,PowerSeries.coeff_mk]; exact Orb.tame_scaleJet ..
lemma dayline (i : Fin r) :
    (∫ x,First.varied Finset.univ o h (fun _=>d) (uncap ∘ p) x i ∂Orb.data G n)=∑ z:Who G d,∑ a:At G r d,∑ b:At G r d,changeR o h p (i,z) a b := by
  simp_rw [dayW]; rw [integral_finsetSum]
  · apply Finset.sum_congr rfl; intro z _
    have H := (court o h (dict (i,z) p) _ (echo_tame o h z i)).symm
    apply H.trans
    have he (a b:Pr G n) (hv:a.2=b.2) := echo_clear (snow a) (snow b) _ (atom_c a) (show oneColor (unitColor G a.2) (snow b) from by rw [hv]; exact atom_c b) (o i) z.val h
    have H0:= two_cost (dict (i,z) p) o h (echoLeg h (o i) z.val) he
    unfold changeR
    dsimp only [Prod.fst,Prod.snd,crestF]; erw [← H0]
  intro z _; exact Orb.Tame.integrable (Orb.Tame.mul (echo_tame o h z i) (First.line_tame ..))
lemma thunder (s v : Ticket) (x : Site n) : Orb.Tame (fun i:Orb.Coords G n=> (↑(tower G x (icon (fresh s) (fresh v)) (spanT i) (spanT i) (spanT i)):ℂ)) := by
  let f (z:Pr G n) := strike (Align.picks (reduced (bead z))) -- picks namespace Align
  have ht (z:Pr G n) (i : Orb.Coords G n): bead z (spanT i)=f z i:= by rw [show f z=strike (Align.picks (reduced (bead z))) from rfl,strike_eq, Align.dot_expand];rfl
  simp_rw [funds3 (A:=spanT _) (B:=tower G x (icon (fresh s) (fresh v))), ht,Complex.ofReal_sum, Complex.ofReal_mul];
  have sums {I : Type} [Fintype I] (g : I→Orb.Coords G n→ℂ) (hg:∀ i,Orb.Tame (g i)):Orb.Tame (fun x=>∑ i:I,g i x) := by rw [show (fun x=> ∑ i:I,g i x)= ∑ i:I,g i from funext fun x=>by rw [Finset.sum_apply]]; exact Orb.Tame.sum fun i _=>hg i
  have H (z : Pr G n): Orb.Tame (fun i:Orb.Coords G n=> (↑(f z i):ℂ)) := (Orb.Tame.clm _).ofReal
  exact sums _ fun a => sums _ fun b=> sums _ fun t=> (((Orb.Tame.constant _).mul (H a)).mul (H b)).mul (H t)
lemma coverline :
   (∫ x,Pert.First.cubic x*First.line Finset.univ o h (fun _=>d) (uncap ∘ p) x ∂Orb.data G n)=∑ a:At G r d,∑ b:At G r d,∑ c:At G r d,verbR o h p a b c := by
  have eh:= court o h p Pert.First.cubic (Pert.First.cubic_tame (G:=G) (N:=n)); rw [← eh];
  let r₂ (x : Site n) (u v : Ticket) := tower G x (icon (fresh u) (fresh v))
  let f (x : Site n) (s v : Ticket) (z : Ribs G n r d) := (↑((r₂ x s v) (spanT z.fst) (spanT z.fst) (spanT z.fst)):ℂ)*spend (teams o h) (feed p) z
  have hu (x : Site n) (s v : Ticket) : Integrable (f x s v) (hall G n r d h) := pre_prices h o p _ (thunder (G:=G) s v x)
  have he (x:Site n) (s v:Ticket): ∫ z,f x s v z ∂hall G n r d h= ∑ i:At G r d,∑ j:At G r d,∑ k:At G r d,(↑((r₂ x s v) (cloudK h o i) (cloudK h o j) (cloudK h o k)):ℂ)*ZeroR o h (dict k (dict j (dict i p))) := by
    apply three_cost _ o h (r₂ x s v) (fun _ _ _=> tower_sym ..) (fun _ _ _=> tower_cross ..); intro a b h z; exact tower_clean x _ _ _ _ _ (atom_c a) (show oneColor (unitColor G a.2) _ from by rw [h]; exact atom_c b)
  have hxw (z:Ribs G n r d): Pert.First.cubic z.fst*spend (teams o h) (feed p) z= ((↑(1/2:ℝ):ℂ)*(∑ x,∑ s,∑ v,f x s v z)) := by simp only [Pert.First.total_vertex,← crown_first,wheels,f,spanT,r₂,Complex.ofReal_sum, ← Finset.sum_mul,Complex.ofReal_mul,mul_assoc]
  simp_rw [hxw]; rw [integral_const_mul,
    integral_finsetSum _ (fun x _=>integrable_finsetSum _ fun u _=>integrable_finsetSum _ fun v _=>hu x u v)]
  simp_rw [integral_finsetSum _ (fun _ _=>integrable_finsetSum _ fun _ _=>hu ..), integral_finsetSum _ fun _ _=>hu ..,he]
  -- permutation paired blocks
  let I := At G r d
  let X:= Site n
  have heq {g:X→Ticket→Ticket→I→I→I→ℂ} :
       ∑ x,∑ t,∑ u,∑ i,∑ j,∑ k,g x t u i j k=∑ i,∑ j,∑ k,∑ x,∑ t,∑ u,g x t u i j k := by
     let B (x : X×Ticket×Ticket) (y : I×I×I) := g x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2
     have e : (∑ x:X×Ticket×Ticket,∑ y:I×I×I,B x y)=∑ y:I×I×I,∑ x:X×Ticket×Ticket,B x y:= Finset.sum_comm
     simp_rw [Fintype.sum_prod_type] at e ⊢; exact e
  rw [heq (g:=fun x u v i j k=>(↑((r₂ x u v) (cloudK h o i) (cloudK h o j) (cloudK h o k)):ℂ)*ZeroR o h (dict k (dict j (dict i p))))]; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; simp only [verbR,r₂,wheels, Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul, Finset.mul_sum, mul_assoc]; rfl
lemma orbital_one (hg : G.Simple) : renda o h p=(∑ a:At G r d,∑ b:At G r d,∑ c:At G r d,verbR o h p a b c)+∑ a:At G r d,∑ b:At G r d,∑ c:At G r d,changeR o h p a b c := by
  rw [renda, recipe_at]; change First.first _=_; rw [First.first_amplitude _ _ _ _ _ hg,First.exposed,coverline]; simp_rw [dayline]; apply congrArg _; exact (Fintype.sum_prod_type (fun a:At G r d=>∑ b:At G r d,∑ c:At G r d,changeR o h p a b c)).symm
end YM.RG11.FirstW.Deck
