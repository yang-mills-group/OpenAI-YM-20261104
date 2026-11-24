import YM.FVA2.Position.Unit
/-! # Unit earmarked on Edit acts at zero horizon (only before H constraints). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Ace
open Function Set Filter Finset MeasureTheory Lattice Wilson
open MS MS.Momentum MS.Arts MS.Koszul MS.Plane MS.Theater MS.Garment MS.Wind
open MS.Pearl MS.Rock MS.Alps MS.Halo MS.Mach MS.Motif MS.Native.Paint
open MS.Hem MS.Hem.Mell MS.Dock MS.Train _root_.YM.MS.Shine MS.High MS.High.Knobs
open MS.Outlook MS.Color MS.Native MS.Native.Wilsonian MS.Landau MS.Landau.Detect
open MS.Book MS.Book.Program MS.Book.Convolve MS.Heat MS.Local.Physical MS.Land
open Garment.Wave Garment.Wick MS.Emit MS.Cylinder MS.Cylinder.Lab MS.Menus MS.City
open MS.Tone MS.Tone.Frame MS.Logarithm Favors
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n:ℕ}{G:Gauge}{w:ℤ}(p:Team)
local notation "B₀"=> Press.portDeck G
local notation "Ω"=> Plaid (Press.portDeck G) 0
-- unit-linear register. Need accounting for proof. `M → amend`.
def active (P:Plaid B₀ 0) : Acts B₀ 0 := UnitF ( Wind.Leading.script (Land.read P) 0 ).val
lemma fit (P:Ω): Leading.FitOrder (Land.read P) (active P 0):= ( Wind.Leading.script (Land.read P) 0 ).property rfl
lemma register (P:Ω)(u:Glyph B₀ 0): ( active P n).register u=if n=0∧u=Land.read P then 1 else 0:= by cases n <;> simp [active, UnitF,Wind.Leading.script]; rfl
lemma vatican (P:Ω)(x:ℝ) : (active P n).proof.input x=0:= by cases n<;>rfl
variable (Y:XSpace.Initialize G)
local notation "ℳ"=> Press.wickInput Y
-- unit row $Z_t$.
lemma score_l (P:Ω)(t:ℝ)(h:film B₀ P.2 (h:=0)= MvPolynomial.C (t:ℂ)): scoreF ℳ p (active P)=fun _=> UnitF (Cylinder.piece (t:ℂ)) := by
   funext s m; unfold scoreF; rw [Pi.add_apply,sky]; simp_rw [vatican,map_zero, Finset.sum_const_zero, add_zero]; unfold Menus.rentF oil; simp_rw [register]; rw [Finset.sum_eq_single (Land.read P)]
   · rw [Finset.sum_eq_single (0,m)]
     · rw [if_pos ⟨rfl,rfl⟩,Polynomial.eval_one,Complex.ofReal_one, one_smul,glo p Y P t h];
     · intro j h ht; obtain he:= Finset.mem_antidiagonal.mp h; simp only [and_true]; rw [if_neg (show j.1≠0 from fun h=> ht (Prod.ext h (by omega))),Polynomial.eval_zero,Complex.ofReal_zero, zero_smul]
     simp
   · intro i _ ht; exact Finset.sum_eq_zero (fun j _=> by rw [if_neg (fun h=> ht h.2), Polynomial.eval_zero, Complex.ofReal_zero,zero_smul])
   simp
lemma sightsH (G:Gauge) (t:ℝ)(n:ℕ): Tone.run ((UnitF (Cylinder.piece (t:ℂ)):T (Dot G Cover)) n)= UnitF (coin (A:=Lane4 G) (t:ℂ)) n:= by cases n with| zero=> exact coin_turn ..| succ k=>exact map_zero _
def estate (G:Gauge)(t:ℝ) : Dec G:= fun i _ _=> UnitF (coin ( t:ℂ)) i
lemma notBusy (t:ℝ)(n:ℕ)(F:Dec G) : path 1 n 0 F (estate G t)=0:= by
    unfold path; rw [ one_smul ]; refine Finset.sum_eq_zero (fun j _=>?_); funext x y; change boulevard Landau.parity (Cpu G y) _ (UnitF (coin (t:ℂ)) j)=0; cases j with| zero=> exact tree_p _ _ _| succ j=> exact map_zero _
lemma laptext (t:ℝ)(n:ℕ) (x y:ℝ) (hp:TouchF (estate G t n x)): Wiref G (estate G t n x) y=0:= by
    change orbit _ _ (estate G t n x y)=0 -- ambiguous
    cases n with| succ n=> exact map_zero _ | zero=> rw [finite_cc μzone (period0 μzone cour0 (main_f G) hp)]; ext l; unfold Ccy; simp [Plane.Flux.at_trc,estate,UnitF,coin]
lemma utility (P:Ω)(t:ℝ)(h:film B₀ P.2 (h:=0)= MvPolynomial.C (t:ℂ)): horizonF ℳ p (active P) =estate G t:= by
   have he i : Fees false 0 (estate G t i):= by
        apply (show _→Fees false 0 (estate G t i) from ?_ ) ( openOrigin (scoreF ℳ p (active P)) i ( decorF ℳ p (active P))); -- pack: rewrite Origin as equality of functions.Lit.
        intro hu; rw [score_l p Y P t h] at hu; change Fees false 0 (fun (x:ℝ) (y:ℝ)=> Tone.run (UnitF ( Cylinder.piece ( A:=LightMode G Cover ) ( t:ℂ ) ) i)) at hu; simp_rw [ sightsH G t ] at hu; exact hu
   have hu : Wind.PM (scoreF ℳ p (active P)) (skyline G p) (estate G t) 0:= ⟨he, ?_⟩; swap; · intro i x; rw [score_l p Y P t h,sightsH G t,notBusy]; refine ⟨rfl,fun j=>?_⟩; rw [laptext _ i _ j (he i|>.stay x|>.joint)]; simp_rw [ Pi.zero_apply, zero_add]; exact fun _=>hasDerivAt_const j _
   funext i; exact mark_birth ( aquaF ℳ p (active P)) hu (fun i hi x=>rfl) i (Nat.lt_succ_self i)
lemma ms_s (P:Ω)(t:ℝ)(h:film B₀ P.2 (h:=0)=MvPolynomial.C (t:ℂ)): (( OpenAxis.Plot B₀).optics 0 P)= Finsupp.single 0 ( pawnMob G t ):= by
    apply OpenAxis.ticket_eq; intro z; rw [ Literal.value_sl,pow_zero,one_smul ]; change Literal.value _ z (OpenAxis.invoice _ _ _ _) =_; rw [OpenAxis.priceR, (show (Resume _ _ _ _).val=_ from h), OpenAxis.sightC ]; -- inspect
variable (S:MS_Data G ( OpenAxis.Plot (Press.portDeck G) ))
lemma steady (P:Ω)(t:ℝ)(h:Theater.film B₀ P.2 (h:=0)=MvPolynomial.C (t:ℂ)): ∀ m,Pact ( UnitF ( baseFlat G t ) m ) (S.marks 0 P m):= by
    obtain ht := S.markOK 0 P; rw [ms_s P t h, (show gloss (Literal.linear (Mob G) (Finsupp.single 0 (pawnMob G t)))=UnitF (Brace G t) from ?_)] at ht; exact (unique_M (once t S.bulk) ht (fun _ _=> EventuallyEq.rfl)).2; funext i j; cases i <;> simp [Literal.hiss,UnitF,Emit.gloss,Brace]
lemma title (P:Ω) (t:ℝ)(h:film B₀ P.2 (h:=0) =MvPolynomial.C (t:ℂ)): col (estate G t)= Archive 0 ( S.marks 0 P ):= by
    funext i y; obtain ⟨u,v⟩:= y; have ht: Shine.Lift ( Parade ( S.marks 0 P i ) 0 u v ) ( UnitF (pawnMob G t) i ):= Shine.Lift.congr (f:=Parade (UnitF (baseFlat G t) i) 0 u v) (F:=UnitF (pawnMob G t) i) ?_ ( prom (steady S P t h i) 0 v u );
    · obtain he:= Shine.Lift.unique ht (live0 (gang ( S.markOK 0 P i )|>.dost)); rcases i with _|i <;> exact congr_fun he 0
    cases i with| zero=> exact stays_p ..| succ i=> change Shine.Lift ( Parade (0:Flats G) 0 _ _) 0; rw [pageZ]; exact Shine.Lift.zero
lemma stack_P {B: Recount G}(P:Ω)(hv:Fixed B (Archive 0 (S.marks 0 P)) false 0 0): Fixed (col (horizonF ℳ p (active P))) (Archive 0 ( S.marks 0 P )) false 0 0:= by
   obtain ⟨t,h⟩:= cost0 P; rw [utility p Y P t h,title S P t h]; intro n hn r H E _ _ w hw ht; exact Like.same (fun i=> (Plane.at_start p_gain.le i).1.le) (hv n hn r H E w hw ht).std
-- set Unit. option dependent. easier match d.
def amen (A:Prescription B₀): Prescription B₀ where
    team:=A.team
    fees d:= match d with| 0=> active | d+1=> A.fees (d+1)
    init d i := by cases d; exact fit ..; exact A.init ..

structure UnitP (A:Prescription B₀): Prop where
    aq (i:Plaid ( Press.portDeck G ) 0): ∀ n, ( A.fees 0 i n ).register = ( active i n ).register
lemma horiz (A: Prescription B₀) : UnitP (amen A) := ⟨fun _ _=>rfl⟩
theorem correct (A:Prescription B₀)(h:TaylorOKF S (Press.wickInput Y) A) : TaylorOKF S (Press.wickInput Y) (amen A):= by constructor; exact h.bulk; intro d i; cases d; exact stack_P A.team Y S i (h.mark 0 i); exact h.mark _ i
lemma same (X:Prescription B₀) (a:Ω) : (X.fees 0 a 0).register=(active a 0).register:= by
 funext i; have ht: ( read a ).grade ≤ i.grade:= Nat.le_trans ((read a).memory) (Nat.zero_le _); simp only [ ( X.init 0 a ).Single i ht,( fit a ).Single i ht]
lemma strictU (A:Prescription B₀)(hp:Horder A): Horder ( amen A ):= by
 constructor; intro d; cases d with| succ d=> exact hp.property (d+1)
                                    | zero=> intro i s n; cases n with
                                                         | zero=> change Favors.move s (fun j=> ( active j 0 ).register ) i=erect s (active i 0).register; simp_rw [ ← same A ]; exact hp.property 0 i s 0
                                                         | succ n=> change Favors.move s (fun _:Ω=> (0:Menus.Price B₀ 0) ) i= erect s (0:Menus.Price B₀ 0); funext i; simp [ Favors.move, Favors.erect ]
-- concrete choice producing same Team, strong field-frame. Unit. compatibility later.
structure Sag (A: Prescription B₀) : Prop where
    Taylor : TaylorOKF S (Press.wickInput Y) A
    still : Horder A
    base : UnitP A

lemma liveM (h:G.Simple): ∃ A,Sag Y S A:=by
 obtain ⟨A,hA⟩:= High_stopsF h S (Press.wickInput Y); obtain ⟨hx,hs⟩:= Favors.upgrades Y S A hA; exact ⟨amen ( Norm₀ A ),correct Y S _ hx, strictU _ hs, horiz _⟩
end YM.FVA2.Position.Ace
