import YM.RegulatorIR.Axial.Unlock

/-! Polynomial moment extraction, W1 over real: single weight variable
suffices before polarization. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {f:Side}{G:Gauge}{W I: Type}{p e i k m n r s:ℕ}

def regalia (σ:Cover→G.Color) : BEdge G:=fun x=> σ x.1-σ (x.1+step x.2)
def chargeT (T:Packet I r)(u:Fin r→I→ℝ):ℝ:= ∑' x:Tuple I r,T x* ∏ i,u i (x i)
def matchT (T:Packet (Foot G) r)(A: Fin r→BEdge G):= chargeT T (fun i=> hue (A i))
def oblique (T:Packet (Foot G) r) (A : BEdge G):=matchT T fun _=>A

lemma bold (T:Packet I r) (f : I→ℝ) : rhyme (vow (fun _=>f)) T e= if e=0 then chargeT T (fun _=> f) else 0:=by
 have hp x:vow (fun _=>f) x=PowerSeries.C (f x):= tale_const _
 unfold rhyme pip; simp_rw [hp, ← map_prod,PowerSeries.coeff_C]; split_ifs <;> first|rfl|simp
lemma horizonT (T:Packet (Foot G) r)(A : BEdge G)(σ:Cover→G.Color): rhyme (vow (shadowU A σ)) T 0= oblique T (A+regalia σ):=by
 have h(x:Foot G) : coeff 0 (vow (shadowU A σ) x)=hue (A+regalia σ) x:=by
    unfold vow; rw [tale_base]; unfold shadowU hue; rw [crest_origin]; apply congr_arg (fun x:G.Color=> x _)
    unfold violet;dsimp only;unfold regalia;rw [Pi.add_apply];abel
 unfold rhyme; simp_rw [pip, PowerSeries.coeff_zero_eq_constantCoeff_apply,map_prod,← PowerSeries.coeff_zero_eq_constantCoeff_apply,h]; rfl
lemma oblique_rate (T:Packet (Foot G) r)(A:BEdge G)(x:ℝ): oblique T (x • A)=x^r*oblique T A:=by
 unfold oblique matchT chargeT hue; simp_rw [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,Finset.prod_mul_distrib]; rw [← tsum_mul_left];apply tsum_congr; intro i; rw [prod_const,card_univ,Fintype.card_fin, mul_left_comm]
lemma rhyme_span (T:Packet (Foot G) r) (A:BEdge G)(σ :Cover→G.Color)(x:ℝ)(i:ℕ): rhyme (vow (shadowU (x • A) (x • σ))) T i= x^(r+i)*rhyme (vow (shadowU A σ)) T i:=by
 let v:=vow (shadowU (x • A) (x • σ));let V:=vow (shadowU A σ)
 have he (p:Foot G)(i): coeff i (v p)=x^(1+i)*coeff i (V p):=by
    change coeff i (routeS _ _ (violet (x • A) _ _))= _* coeff i (routeS _ _ _)
    rw [song_jet,song_jet,show violet (x • A) (x • σ) p.1= x • violet A σ p.1 from rfl]; unfold song; rw [jet_smul, Nat.add_comm 1]
 have hp(n:ℕ)(k:ℕ)(w:Tuple (Foot G) n): coeff k (pip v w)= x^(n+k)*coeff k (pip V w):=by
    induction n generalizing k with
    | zero=>
       by_cases hk:k=0; rw [hk]; simp [pip]; simp [pip,hk]
    | succ n ih=>
       rw [show pip v w= v (w 0)*pip v (Fin.tail w) from Fin.prod_univ_succ _,show pip V w= _ from (Fin.prod_univ_succ (fun i=> V (w i))),coeff_mul,coeff_mul, Finset.mul_sum]
       apply sum_congr rfl; intro i hi; have h:=mem_antidiagonal.mp hi
       change coeff _ _ * coeff _ (pip v _) = _*(_* coeff _ (pip V _))
       rw [ih,he,show n+1+k=(1+i.1)+(n+i.2) by omega,pow_add];unfold Fin.tail; ring
 unfold rhyme;change ∑' p,T p*coeff i (pip v p)=_;rw [← tsum_mul_left]; apply tsum_congr; intro p; rw [hp,mul_left_comm]

-- directions always evaluated in Lock.G.
def directionsX (U:Orders (Foot G))(A:BEdge G)(σ:Cover→G.Color)(i r:ℕ):ℝ:=∑ j∈ antidiagonal i,∑ s∈ range (j.1+2+1), if s+j.2=r then rhyme (vow (shadowU A σ)) (U j.1 s) j.2 else 0
lemma chronicles (U:Orders (Foot G))(A:BEdge G)(σ:Cover→ G.Color)(x:ℝ): rhymeR (vow (shadowU (x • A) (x • σ))) U 2 e=∑ i∈ range (e+2+1),x^i*directionsX U A σ e i:=by
 unfold rhymeR directionsX; simp_rw [Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i hi;rw [sum_comm]; apply sum_congr rfl; intro j hj
 rw [rhyme_span, Finset.sum_eq_single_of_mem (j+i.2) (by have hp:= Finset.mem_antidiagonal.mp hi; rw [Finset.mem_range] at hj ⊢;omega),if_pos rfl]; intro b _ he;rw [if_neg he.symm,mul_zero]
lemma traverses (U:Orders (Foot G))(A:BEdge G) : rhymeR (vow (fun _=>hue A)) U 2 e= ∑ i∈range (e+2+1),oblique (U e i) A:=by
 unfold rhymeR; rw [sum_eq_single_of_mem (e,0) (by simp)]; simp_rw [bold]; simp only [↓reduceIte];rfl
 intro i hi he; have hp:=mem_antidiagonal.mp hi; simp_rw [bold,if_neg (show i.2 ≠ 0 from fun h=>he (Prod.ext (by change i.1=e;omega) h))]; simp
lemma trav_span (U:Orders (Foot G))(A:BEdge G)(x:ℝ): rhymeR (vow (fun _=>hue (x • A))) U 2 e=∑ i∈range (e+2+1),x^i*oblique (U e i) A:=by rw [traverses];simp_rw [oblique_rate]
lemma ext_power (F P : ℕ→ℝ)(S:Finset ℕ)(h:∀ x:ℝ,∑ i∈ S,x^i*F i= ∑ i∈ S,x^i*P i) (hS:i∈S): F i=P i:=by
 let f(Φ:ℕ→ℝ): Polynomial ℝ:= ∑ i∈S,Polynomial.X^i*Polynomial.C (Φ i)
 have hh : f F=f P:= Polynomial.funext fun x=> by
    unfold f; simp_rw [Polynomial.eval_finsetSum, Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]; exact h x
 have hp(g:ℕ→ℝ) : (f g).coeff i=g i:=by
    unfold f; rw [Polynomial.finsetSum_coeff,Finset.sum_eq_single_of_mem i hS]; simp
    intro j _ hj; rw [Polynomial.coeff_mul_C];simp [Polynomial.coeff_X_pow,Ne.symm hj]
 rw [← hp F,← hp P,hh]
lemma flashes {A:BEdge G}(h:(Function.support A).Finite)(x:ℝ) : (Function.support (x • A)).Finite:= h.subset (by intro i hi; exact fun hh=>hi (by simp [hh]))
lemma flashes' {A:Cover→G.Color}(h:(Function.support A).Finite)(x:ℝ) : (Function.support (x • A)).Finite:= h.subset (by intro i hi; exact fun hh=>hi (by simp [hh]))

namespace WOne
variable {U: Orders (Foot G)}(H:W1 U p)
variable {e r:ℕ}(he:e≤p)(hr:r ≤ e+2)(A:BEdge G)(h:(Function.support A).Finite)
include H h he hr
lemma travels (u:Signed) : oblique (U e r) (beast u A)=oblique (U e r) A:=by
 refine ext_power (fun i=> oblique (U e i) _) (fun i=> oblique (U e i) _) (range (e+2+1)) ?_ (Finset.mem_range.mpr (by omega))
 intro t;rw [←trav_span,←trav_span,← H.signed (t • A) (flashes h t) u e he,show beast u (t • A)=t • beast u A from funext (fun i=>by rw [Pi.smul_apply (f:=beast u A)]; unfold beast; split <;> first| (rw [smul_neg]; rfl)|rfl)] -- occ inspect
lemma fares (u:G.El) : oblique (U e r) (vbadge u A)=oblique (U e r) A:=by
 apply ext_power (fun i=>oblique (U e i) _) (fun i=>oblique (U e i) _) (range (e+2+1)) _ (Finset.mem_range.mpr (by omega));intro t
 rw [←trav_span,←trav_span,← H.adjoints (t • A) (flashes h t) u e he,show vbadge u (t • A)=t • vbadge u A from funext fun i=>(G.adjoint u).map_smul t (A i)]
variable (σ:Cover→ G.Color)(hv:(Function.support σ).Finite)
include hv
lemma gathers : directionsX U A σ e r= oblique (U e r) A:=by
 refine ext_power (directionsX U A σ e) (fun i=> oblique (U e i) A) (range (e+2+1)) (fun x=>?_) (Finset.mem_range.mpr (by omega)); rw [←chronicles,←trav_span]; exact H.grade _ _ (flashes h x) (flashes' hv x) e he
-- cost on lower valuation without rank qualification

def sweep (U:Orders (Foot G))(e r:ℕ)(A:BEdge G)(σ:Cover→G.Color):= ∑ j∈ (antidiagonal e).erase (e,0),∑ i∈ range (j.1+2+1),if i+j.2=r then rhyme (vow (shadowU A σ)) (U j.1 i) j.2 else 0
lemma supps : oblique (U e r) (A+regalia σ)= oblique (U e r) A-sweep U e r A σ:=by
 rw [eq_sub_iff_add_eq,← gathers H he hr A h σ hv]; unfold sweep directionsX; rw [← add_sum_erase (antidiagonal e) (fun _=>_) (show (e,0) ∈ Finset.antidiagonal e from by simp)]; apply congr_arg (· + _); symm; rw [sum_eq_single_of_mem r (Finset.mem_range.mpr (by omega)),if_pos (by simp)]; exact horizonT ..
 intro _ _ h; rw [if_neg (by simpa using h)]
end WOne
end YM.RegulatorIR.Pupil
