import YM.RegulatorIR.Axial.Brief

/-!
# Insert kinetic even across winding anomalies
Rank zero vacuum omitted entirely from W1 (not source). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck Matrix
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {X Y:Type}{G:Gauge} {i k e r:ℕ}{f:Side}

def twosM (X:Type) : (X×X) ≃ Tuple X 2 where
 toFun x:=![x.1,x.2]
 invFun i:=(i 0,i 1)
 left_inv x:=by rcases x with ⟨x,y⟩; rfl
 right_inv i:=funext fun x=> by fin_cases x <;> rfl

def coil (K:Layer X X): Packet X 2:=fun z=>(-1/2:ℝ)* K (z 0) (z 1)
def dyeX (K:Layer X X) (T:Orders X):Orders X:= fun i r=>if h:i=0 ∧ r=2 then h.2.symm ▸ coil K else if r=0 then 0 else T i r
def profitX (K:Layer X X)(T: Orders X)(x:X→PowerSeries ℝ)(i:ℕ):= rhymeR x (dyeX K T) 2 i
lemma jetInk (K:Matrix (Book G f) (Book G f) ℝ) (x : ℝ→ Horizon G f) (h:ContDiffAt ℝ ∞ x 0) : rhyme (vow (peel x)) (coil K) k= coeff k (tale (steam K ∘ x)):= by
 let v:= peel x; let T:= coil K
 have he : steam K ∘ x = filament (render T) v:=by
    ext1 i; unfold filament; rw [← pluck]; unfold strum
    let u:= v i
    change -((u ⬝ᵥ (K*ᵥ u))/2)=∑'z,T z * _ -- inspect (sum?)
    rw [← (twosM _).tsum_eq]; simp_rw [tsum_fintype];rw [Fintype.sum_prod_type]
    unfold dotProduct mulVec dotProduct; simp_rw [Finset.mul_sum,Finset.sum_div,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; change -( (_ * _) /2)= (-1/2)*K j k * _; unfold noodle; rw [Fin.prod_univ_two]; change -( (u j*(K j k*u k))/2)= (-1/2)*K j k*(u j*u k); ring
 rw [he,Halo.slim,rhyme_f];rfl
 exact contDiffAt_pi.mpr (Ward.RangeR.lifts h)
section Coil
variable {P:ℝ}(A:Deck P X Y) (K:Layer X X) (H:Layer.Sym A A K)
include H
lemma coil_r : A.Ready (coil K):=by intro d x; unfold Deck.dyed coil; change (-1/2:ℝ)*K (A.wind d (x 0)) (A.wind d (x 1))*_= _; rw [H, Deck.polish_mov, pow_two]; rw [Motion.sign_sq,one_mul] -- name
lemma deck_costA (p:Tuple Y 2) : A.deckSum (coil K) p=coil (fmat A A K) p:=by
 let x:= A.place (p 0)
 rw [deck_pivot _ (coil_r A K H) _ 0 x (A.placed _)]; unfold lodge
 let f(i: Deck.Nest A p 0 x): Stalk A.orbit (p 1):= ⟨i.val 1,congr_fun i.property.1 1⟩
 let E : Deck.Nest A p 0 x≃ Stalk A.orbit (p 1):= Equiv.ofBijective f ⟨(fun i j h=>Subtype.ext (funext (fun k=>by fin_cases k;exact i.property.2.trans j.property.2.symm;exact congr_arg (fun l=>l.val) h))), fun j=>⟨⟨twosM X (x,j.val),by ext1 i;fin_cases i;exact A.placed _;exact j.property,rfl⟩,Subtype.ext rfl⟩⟩
 unfold coil fmat wrapL forwardCost Stalk.collect; rw [← tsum_mul_left,← E.tsum_eq];apply tsum_congr;intro p; unfold dyed polish paint; rw [Fin.prod_univ_two,p.property.2]; change (-1/2:ℝ)*_*_=_; rw [mul_assoc,p.property.2]; rfl
omit H A in
lemma coil_f (H:Billed K)(x:X) : Summable fun i:Hold (0:Fin 2) x=> ‖coil K i.val‖:=by
 let p(h:Hold (0:Fin 2) x): X:=h.val 1
 let k(y:X):= ‖-(1:ℝ)/2‖*‖K x y‖
 have hk: Summable k:= by refine Summable.mul_left _ (tsum_enorm_ne_top_iff_summable_norm.mp ?_); rw [← quota_base]; exact H.rows x
 have hh(i:Hold (0:Fin 2) x): ‖coil K i.val‖=k (p i):=by unfold coil k; rw [show i.val 0=x from i.property,norm_mul]
 simp_rw [hh]; exact hk.comp_injective (fun i j h=>Subtype.ext (by ext1 y;fin_cases y; exact i.property.trans j.property.symm; exact h))
end Coil
-- no r=0 reading unless passed rank position
variable (K:Layer X X)(T:Orders X)
lemma profit_sum {a:X→PowerSeries ℝ}(h: Vacuum T) : profitX K T a i=rhyme a (coil K) i + rhymeR a (pulp T) 2 i:=by -- i
 let f (j:ℕ×ℕ):= ∑ r∈ Finset.range (j.1+2+1), rhyme a (dyeX K T j.1 r) j.2;let t(j:ℕ×ℕ):= ∑ r∈Finset.range (j.1+2+1), rhyme a (pulp T j.1 r) j.2
 have ht(j):t (0,j)=0:=by unfold t; apply Finset.sum_eq_zero;intro r _; have hh : pulp T 0 r=0:= (vacuum_lo _ (eraseVac T h)) ▸ rfl; rw [hh];simp [rhyme]
 have hx (j):f (0,j)=rhyme a (coil K) j:=by
    unfold f; rw [Finset.sum_eq_single_of_mem 2 (by change 2∈Finset.range 3;decide)]; simp [dyeX]
    intro k _ hk; rw [show dyeX K T 0 k=0 from by rw [dyeX, dif_neg (fun h=>hk h.2),vacuum_lo T h]; simp]; simp [rhyme]
 have hp (j:ℕ×ℕ)(hj:0<j.1) : f j=t j:= Finset.sum_congr rfl fun r _=>by unfold dyeX pulp;rw [dif_neg (fun h=>hj.ne' h.1)] -- pulp exact
 unfold profitX rhymeR; change ∑ j∈Finset.antidiagonal i,f j=rhyme a (coil K) i + ∑ j∈Finset.antidiagonal i,t j -- syntax
 let s:=Finset.antidiagonal i; let v:=((0:ℕ),i); have hz:v∈s:=by simp [v,s]
 rw [← Finset.add_sum_erase s f hz,← Finset.add_sum_erase s t hz,show f v= _ from hx i, ht,zero_add]; apply congr_arg; apply Finset.sum_congr rfl;intro i' hi; apply hp i'
 obtain ⟨hx,hy⟩:= Finset.mem_erase.mp hi; have hh:= Finset.mem_antidiagonal.mp hy; unfold v at hx; rcases i' with ⟨n,k⟩; simp only at *; rcases Nat.eq_zero_or_pos n with rfl|ht; exact (hx (congr_arg _ (by omega : k=i))).elim; exact ht
end YM.RegulatorIR.Axial
