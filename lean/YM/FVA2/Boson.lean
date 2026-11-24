import YM.FVA2.Berezin
import YM.AllOrder.Haiku.Projection
import YM.FormalOPE.RG10.MultiGauge.Engine

/-!
# Embed the RG10 polynomial ticket algebra (all coupling orders) faithfully for Wick evaluation

Only bosonic directions. All calculus at the local origin. Key distinction from `paper` rank caps:
 compare **full jets at every order** including higher derivatives (and inserted ranks). `mask` is
 not a projection of placement. It extracts exactly the iteratedFDeriv(Taylor) polynomial level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Boson
open Filter PertExtension Function FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open MS MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater Finset PowerSeries PairCoords Paper
open scoped Topology Classical ContDiff
variable {E U A:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (e:A→E) (p:Sector A)(h:∀ i,p i=true→e i=0)

lemma paper_hot (g: Permit E) : ContDiff ℝ ω g.val:= by apply Papers.induction (P:=fun v:E→ℝ=>ContDiff ℝ ω v) (fun f=> f.toContinuousLinearMap.contDiff) (fun _=> contDiff_const) (fun _ _ _ _ hf hg=>hf.add hg) (fun _ _ _ _ hf hg=>hf.mul hg) g.property

def billInk (e:A→E)(p:Sector A)(h:∀ i,p i=true→e i=0) : Permit E→+* Dark p where
    toFun a:= ⟨ ink e a.val,Taylor.ink_p _ h _ ⟩
    map_zero':=Subtype.ext (Taylor.ink_zero _)
    map_one':=Subtype.ext (Eq.trans (Taylor.ink_const e (1:ℝ)) (by rw [Complex.ofReal_one]; rfl))
    map_add' x y:= Subtype.ext (ink_add e (paper_hot x|>.contDiffAt) (paper_hot y|>.contDiffAt))
    map_mul' x y:= Subtype.ext (ink_mul e h (paper_hot x|>.contDiffAt) (paper_hot y|>.contDiffAt))

def sharp : PowerSeries (Permit E) →+* Price p := PowerSeries.map (billInk e p h)

lemma sharp_coe (F: PowerSeries (Permit E))(k:ℕ) : Paper.track p (sharp e p h F) k=ink e (coeff k F).val := by rw [tracking,sharp,coeff_map]; rfl

-- coefficients of iteratedFDeriv on list suffice (for arbitrary e:A→E, non-spanning)
-- we *reverse* list of directions to match S2 calculus; lower orientation goes at the end using succ formula.

def mot (e:A→E): (k: List A)→ Fin k.length → E | []=> fun i=> i.elim0 | v::l=> Fin.snoc (mot e l) (e v)
omit [FiniteDimensional ℝ E] in
lemma entry (f:E→ℝ)(hx: germ f)(l:List A): ink e f l= Complex.ofReal (iteratedFDeriv ℝ l.length f 0 (mot e l)):= by
   induction l generalizing f with
   | nil=> simp [mot]
   | cons i l ih=>
       let P:= ContinuousLinearMap.apply ℝ ℝ (e i); have hl:= P.iteratedFDeriv_comp_left (hf:= hx.fderiv_right (m:=ω) le_top ) (i:=l.length) le_top;
       have h' : ink e f (i::l)= _:= ih (layer (e i) f) (germ_layer hx _)
       rw [h']; change Complex.ofReal ((iteratedFDeriv ℝ l.length (P ∘ (fderiv ℝ f)) 0) (mot e l))= _
       rw [hl, show iteratedFDeriv ℝ (i::l).length f 0 (mot e (i::l))= _ from iteratedFDeriv_succ_apply_right (n:=l.length) ..]; rw [mot,Fin.init_snoc,Fin.snoc_last]; rfl

lemma paper_level (f:E→ℝ)(k:ℕ): ContDiffAt ℝ ω (PertExtension.Series.Radial.jet f k) 0:= (paper_hot (⟨ _,Papers.jet_poly f k ⟩ : Permit E)|>.contDiffAt)
lemma masked (f:E→ℝ)(H:germ f)(k:ℕ): mask k (ink e f)=ink e (PertExtension.Series.Radial.jet f k) := by
   funext l
   rw [entry _ _ (paper_level f k)]
   by_cases hk:l.length=k
   · rw [enough _ (by omega), entry _ _ H, show iteratedFDeriv ℝ l.length _ _=_ from (?_)] ; subst k; exact (AllOrder.Haiku.Project.self f H l.length).symm
   rw [ AllOrder.Haiku.Project.other f (Ne.symm hk), strange _ (by omega) ]; simp

lemma lifting (f:E→ℝ)(H:germ f)(k:ℕ): track p (sharp e p h (MultiGauge.Stack.rise f)) k= mask k (ink e f) := by rw [sharp_coe, MultiGauge.Stack.rise, coeff_mk, masked e f H k ]
-- expense (rank). Simple induction all polynomial entries. Use later.
abbrev minted {x:E→ℝ} (hx:x∈ papers E) := (⟨x,hx⟩:Permit E)
omit [FiniteDimensional ℝ E] in
lemma off_one {i:A} (hi:e i=0)(F: Permit E) : Koszul.D i (ink e F.val) = 0 := ink_off e hi _
lemma frameLinear (ℓ: Module.Dual ℝ E)(i:A): D i (ink e ℓ)=coin (ℓ (e i):ℂ):= by
   rw [Taylor.inktip, show layer (e i) ℓ=fun _ => ℓ (e i) from funext (fun x=> congrArg (fun L:E →L[ℝ] ℝ=> L _) (ℓ.toContinuousLinearMap.fderiv (x:=x))),Taylor.ink_const]
lemma frame_fee (ℓ : Module.Dual ℝ E): ink e ℓ ∈ Mini A:= by
  apply minH (v:=1); intro l he; rcases l with _|⟨i,_|⟨a,l⟩⟩ <;> simp only [List.length_nil,List.length_cons,Nat.zero_add,Nat.cast_add,Nat.cast_one,Nat.cast_zero] at he <;> try omega
  rw [D_eval i (ink e ℓ), frameLinear]; rfl
include h
lemma rank_money (F:Permit E): (billInk e p h F).val ∈ FeeP p:= by
   refine ⟨ ink_s _ h (paper_hot F|>.contDiffAt),?_⟩
   change ink e F.val∈Mini A; apply Papers.induction (P:=fun f:E→ℝ=>ink e f∈ Mini A) ?_ ?_ ?_ ?_ F.property
   · exact frame_fee e
   · intro v; rw [Taylor.ink_const]; exact minH (coinN _)
   · intro f g hf hg h1 h2; rw [ Taylor.ink_add e (paper_hot (minted hf)|>.contDiffAt) (paper_hot (minted hg)|>.contDiffAt) ]; exact (Mini _).add_mem h1 h2
   intro f g hf hg h1 h2; rw [ Taylor.ink_mul e h (paper_hot (minted hf)|>.contDiffAt) (paper_hot (minted hg)|>.contDiffAt) ]; exact miPair h1 h2
lemma sharp_bound (F:PowerSeries (Permit E)): Bound (sharp e p h F):= by intro i _; rw [tracking,sharp,coeff_map]; exact rank_money _ _ _ _
lemma sharp_omits (F:PowerSeries (Permit E))(i:A)(he:e i=0): Omits i (sharp e p h F):= by intro k; rw [sharp_coe]; exact off_one e he _
end YM.FVA2.Boson
