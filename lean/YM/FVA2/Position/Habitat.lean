import YM.FVA2.Position.Column
import YM.FVA2.Position.Flight
/-!
# Signed-axis covariance of MS `Archive` for the chosen continuation

See `archiveH` for the comparison at the actual mark bins, at every formal order.
Used before the final comparison at the given scale, e.g. for `Frugal` to average over H
on the fee data while keeping the native cost estimates and coherences.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Park
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Hem.Mell MS.Dock MS.Train MS.Pearl MS.Local.Physical
open _root_.YM.MS.Shine Brass Weft OpenAxis Axes MS.Color Garment.Wave Garment.Wick MS.Heat.Signal Book.Convolve
open MS.Menus MS.Land MS.Mach MS.Emit
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {J:Type}{m n k:ℕ}{G:Gauge}{B F X: T ( Flats G )} (s t:Signed) {p a b d: T ( Coat G )} {q r:ℤ}
-- combinators linear, no matching assumptions.
lemma plusP (h:comet n r B p F a)(hv:comet n r B d X b) : comet n r B (p+d) ( F+X ) (a+b) := by
    intro i; obtain ⟨⟨v,hm,hV,hp⟩,-⟩:= h i; obtain ⟨⟨u,hN,hU,hW⟩,-⟩:= hv i; refine ⟨⟨max v u, ?_, Cap0.heap.plus (clockTrans hV (le_max_left ..)) (clockTrans hU (le_max_right ..)), (hp.collects (le_max_left ..)).add ( hW.collects (le_max_right ..))⟩,False.elim⟩; have he:= hm.plus hN; rw [add_add_add_comm (platform B i F)] at he; simp only [Pi.add_apply,platform,map_add,Finset.sum_add_distrib]; exact he
lemma scaleP (x:ℝ)(h:comet m r B p F a): comet m r B ( x • p ) ( x • F ) ( x • a ) := by
    intro i; obtain ⟨⟨q,hm,hV,hU⟩,-⟩:= h i; refine ⟨⟨q, ?_, fun j=>?_,?_⟩,False.elim ⟩
    · have he:= hm.scale (x:ℂ); rw [smul_add] at he; change Joint m (platform B i ((x:ℂ) • F) + step0 G ((x:ℂ) • F i)) ((x:ℂ) • F i) ((x:ℂ) • p i) ((x:ℂ) • a i); rw [map_smul]; apply Joint.via he; unfold platform; simp_rw [Pi.smul_apply, map_smul,Finset.smul_sum]; exact fun i=>EventuallyEq.rfl
    · exact ( hV _ ).smul (i:=(x:ℂ)) (by simp)
    exact hU.smul (i:=(x:ℂ)) (by simp)
lemma zeroP (F:T (Flats G)):comet m r F 0 0 0:= by intro i; unfold PathD platform; simp only [Pi.zero_apply,map_zero,Finset.sum_const_zero]; exact zero_sing _
lemma collectP (J':Finset J)(B:T ( Flats G )) (m:ℕ){F:J→ T ( Flats G )}{p a:J→ T ( Coat G )}(h:∀ i∈J',comet m r B (p i) (F i) (a i)): comet m r B (∑ i∈J',p i) (∑ i∈ J',F i) ( ∑ i∈J',a i ) := by
    induction J' using Finset.induction with| empty=> simp only [Finset.sum_empty]; exact zeroP B| insert i j he ih=> rw [Finset.sum_insert he, Finset.sum_insert he, Finset.sum_insert he]; exact plusP (h i (by simp)) (ih fun k hk=> h k ( Finset.mem_insert_of_mem hk ))
local notation "V"=> flats_t s⁻¹
local notation "Φ"=> coat_t s⁻¹
local notation "Ω"=> hoop s⁻¹
local notation "Q₀"=> Plot (Press.portDeck G)
local notation "H"=> Press.portDeck G
open MS.Theater MS.Motif.Literal
--- source column P∈Plaid. compact
variable {w:ℕ}
lemma optical (i: Plaid ( Press.portDeck G ) w) : Literal.Boom 0 (hoop s⁻¹) ( (Q₀).optics w i)=∑ j:Case G w i.1.val, markS s G w i.1.val i.2 j • (Q₀).optics w ⟨i.1,j⟩ := by
    -- use literal portraits & film continuation
    apply ticket_eq; intro z; rw [linear_v,map_sum]; simp_rw [Mach.lng ]; ext1 n; conv_rhs=> rw [ Finset.sum_apply  ]
    have he (i: Plaid H w) : value (Mob G) z ( ( Plot H ).optics w i)= seed G (film H i.2 (h:=w)) z:= priceR ( x:= Resume H w _ (baseH G w i.1.val i.2) ); simp_rw [ he ]; change Brass.cash s⁻¹ n _=_; rw [equivariant, Axes.kind, Axes.cast]; simp_rw [map_sum,show ∀ ( x:ℝ)(p:Labels.Pol G), seed G (x • p)=x • seed G p from fun x p=> map_smul ( (seed G).restrictScalars ℝ ) x p, Finset.sum_apply,Pi.smul_apply]
lemma Amt (i:Plaid (Press.portDeck G) w) : (Φ ∘ gloss ( linear ( Mob G ) ( (Q₀).optics w i )))= ∑ j:Case G w i.1.val, markS s G w i.1.val i.2 j • gloss (linear (Mob G) ((Q₀).optics w ⟨i.1,j⟩)) := by
    funext u v; change Ω (((Q₀).optics w i) u) = _; rw [← Literal.whole,optical]; simp only [ Literal.hiss,Finset.sum_apply,Finset.sum_apply', Finsupp.smul_apply,Pi.smul_apply ]; rfl
-- exact all-order identity at that supplied MS continuation.
abbrev rotatedMarks (s:Signed)(S:MS_Data G (Plot (Press.portDeck G)))(w:ℕ)(i: Plaid (Press.portDeck G) w) := ∑ j:Case G w i.1.val, markS s G w i.1.val i.2 j • S.marks w ⟨i.1,j⟩
abbrev rotatedPoles (s:Signed)(S:MS_Data G (Plot (Press.portDeck G)))(w:ℕ)(i: Plaid (Press.portDeck G) w) := ∑ j:Case G w i.1.val, markS s G w i.1.val i.2 j • S.poles w ⟨i.1,j⟩
variable (S:MS_Data G (Plot (Press.portDeck G)))
lemma installed (i:Plaid H w): comet w 0 S.bulk (Φ ∘ gloss (linear (Mob G) ((Plot H).optics w i))) (rotatedMarks s S w i) (rotatedPoles s S w i):= by rw [Amt]; exact collectP _ _ _ (fun j _=> scaleP _ ( S.markOK w ⟨i.1,j⟩))
theorem rotates (i: Plaid H w): Φ ∘ S.poles w i=rotatedPoles s S w i ∧ ∀ n,Pact (V ( S.marks w i n )) ( rotatedMarks s S w i n ) := unique_M (soaring s⁻¹ ( S.markOK w i ) (strongest S.bulkOK)) (installed s S i) (fun _ _=> EventuallyEq.rfl)
-- now instantiate order and horizon symmetric boundaries to compare `Archive`.
lemma level (_S:MS_Data G (Plot (Press.portDeck G))) (F X: Flats G)(h:Stay n X)(hp:Pact F X) (A:Mob G)(y z:ℝ)(he:Shine.Lift (Parade F n y z) A): hereZ n X z y=A:= Shine.Lift.unique (live0 h) (Shine.Lift.congr he (prom hp n z y)) -- pose args check
-- these with arbitrary weighting: need no Booked
lemma sum_L (f:J→ Flats G)(F:Finset J)(a:J→ℝ) (n:ℕ)(hs:∀ j∈F,Stay n (f j))(y z:ℝ): Shine.Lift ( Parade (∑ i∈F,a i • f i ) n y z ) (∑ i∈F,a i • hereZ n (f i) z y):= by
    rw [page_sum]; apply ( show (∀ {F x},Shine.Pick 0 F x→ Shine.Lift (G:=G) F x) from fun ht=>ht); refine Shine.Pick.fin _ (fun i hi=>?_); have hf: Parade (a i • f i) n y z=a i • Parade (f i) n y z:= page_smul (a i:ℂ) (f i) _ _ _; rw [hf]; exact Shine.Lift.static (live0 ( hs i hi )) (a i:ℂ)

lemma Cliff (i: Plaid H w)(n:ℕ)(y z:ℝ): hoop s⁻¹ (hereZ w ( S.marks w i n ) z y)= ∑ j: Case G w i.1.val, markS s G w i.1.val i.2 j • hereZ w ( S.marks w ⟨ i.1,j ⟩ n ) z y:= by
    refine Shine.Lift.unique (f:= Parade (rotatedMarks s S w i n) w y z) ?_ ?_; · apply Shine.Lift.congr (F:= Ω (hereZ w ( S.marks w i n ) z y)) (f:=fun x=>Ω ( Parade ( S.marks w i n ) w y z x )) (sh_h s⁻¹ (live0 ( gang ( S.markOK w i n )|>.dost ))) ?_; rw [ ← show Parade (V (S.marks w i n)) w y z=_ from funext fun x=>card s⁻¹ _ x _ y z ]; exact prom ((rotates s S i).2 n) w z y
    unfold rotatedMarks; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact sum_L (fun j=> S.marks _ ⟨ i.1,j⟩ n ) _ _ _ (fun i _=> (gang ( S.markOK w ⟨ _,i ⟩ n )).dost) _ _

-- directly useful for the mark frame. This works at any real log-scale arguments there.
theorem archiveH (i:Plaid H w)(n:ℕ)(y z:ℝ): (flagS (m:=0) (Outlook.hand s⁻¹) G).beam (Archive w ( S.marks w i ) n (y,z)) = ∑ j: Case G w i.1.val, markS s G w i.1.val i.2 j • Archive w ( S.marks w ⟨ i.1,j⟩ ) n (y,z) := by
    obtain ht:= congr_fun (Cliff s S i n y z) 0; simp only [Finset.sum_apply] at ht; change Weft.lamp (m:=0) _ _= _; rw [← selfA (m:=0) (hand s⁻¹) ]; exact ht
end YM.FVA2.Position.Park
