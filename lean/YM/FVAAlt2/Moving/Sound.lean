import YM.FVAAlt2.Moving.Up
/-! # Intrinsic (no MS) real spelling period bank.
 Exact pose algebra identifies the Plan.Begins bare **columns** at actual lattice regression. Not an identification of all regulator details with those on the constant-q Plan grids & cameras! But used to recover same perturbative answer along the moving schedules at actual apertures.

Use a generic Episode array E (already computed raw basis column products at that period, includes g⁻ᵐ valuation at Native θ but does NOT include engineering weight/profile measure/ W-transform/normalization).
 Instantiate with `perRead` whose legitimacy follows even pre-limit with authentic stencil input. Use same Resource per output query as needed to identify palette.Rank.Mask. `Λ` can be chosen all-arity. Reality exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.Perot
open Function Set Filter MeasureTheory Real Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT Pegs
open MS MS.Land MS.Menus MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open PowerSeries Integration RunFormalChain Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home YM.FVAAlt2.Home.Report
open Function Set Finset Metric Labels Extra.FD Maxwell Source Extraction FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open RG10.Position (Plan Spur Loft)
open PowerSeries (C coeff constantCoeff)
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Z W :Type} [Fintype W][LinearOrder W]{d r:ℕ}{F:Frames G}{H:Source.Hol G} (R:Lobby.Registry F H) (B:Lodge.Track X)(x:X)
local notation "FC"=> PowerSeries ℂ
local notation "ϵ"=> Sound.Alone B x
local notation "V"=> RG10.Position.Deck F d
set_option quotPrecheck false
section list
variable (d: W→ℕ)(T:Sound.Formal.Episode W F)
-- expansion B:Foot.Label input. uses actual basis.Sound.Point not via Θ.Step recurrence here. Θ.period finance follows
abbrev kernel (R:Lobby.Registry F H)(d':W→ℕ)(p:(i:W)→ Label G (d' i))(T:Sound.Formal.Episode W F): FC:= ∑ v:(i:W)→(F.level (d' i)).Index, C (∏ i:W, Home.Profiles.start R ( d' i ) (p i) (v i) ) * T d' v
lemma tall {J:W→Type}[∀ i,Fintype (J i)](f: (i:W)→ J i→ℂ)(P:(i:W)→J i→ Label G (d i)): Perot.kernel R d (fun i=>∑ j,f i j • P i j ) T=∑ v:((i:W)→J i), C ( ∏ i, f i (v i) ) * Perot.kernel R d (fun i=> P i (v i)) T:=by
 have hv (d:ℕ)(j:W)(a:( F.level d ).Index)(Q:J j→ Label G d): Home.Profiles.start R d (∑ k:J j,f j k • Q k) a= ∑ k:J j,f j k * Home.Profiles.start R d (Q k) a:=by
    unfold Home.Profiles.start; rw [map_sum]; simp_rw [ Finset.sum_apply, map_smul, Pi.smul_apply, Finset.sum_mul, Finset.mul_sum ]; rw [Finset.sum_comm]; simp_rw [smul_eq_mul,mul_assoc]
 unfold kernel; simp_rw [hv,Fintype.prod_sum,map_sum,Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_comm]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>by rw [Finset.prod_mul_distrib,map_mul,mul_assoc]
end list
variable {U:MS.Local.Physical.Deck G}
local notation "Ψ" n=> Motor B n x→ Sound.Formal.Episode (Fin n) F
noncomputable abbrev Exhibit (B:Lodge.Track X)(x:X)(F:Frames G): Type:= (n:ℕ)→ Motor B n x→ Sound.Formal.Episode (Fin n) F
variable (T:Exhibit B x F)(g:Fin r→ℕ)(v:(i:Fin r)→Label G (g i))
noncomputable def cost (f:Points r→ℝ) (p:(i:Fin r)→ Label G (g i)):FC:= Pegs.compilation B x (fun b=> C ((ϵ:ℂ)⁻¹ ^ ∑ i,g i) * Perot.kernel R g p (T r b)) f
lemma priced {J:Fin r→Type}[∀ i,Fintype (J i)](f:(i:Fin r)→ J i→ℂ)(v:(i:Fin r)→J i→Label G (g i))(φ:Points r→ℝ): Perot.cost R B x T g φ (fun i=>∑ j, f i j • v i j)=∑ u:(i:Fin r)→J i,C (∏ i,f i (u i))*Perot.cost R B x T g φ (fun i=>v i (u i)) :=by
 unfold cost Pegs.compilation; simp_rw [tall,Finset.mul_sum]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro q _; apply sum_congr rfl; intro v _; ring
variable (P:Plan F)
-- header ⚠ implicit R selected across quantity labels.Sn
noncomputable def Raw (D:ℕ)(v:Home.Datum (RG10.Position.Deck F D)): FC:= Perot.cost (nativeR P) B x T (fun i=> (RG10.Position.Deck.token F D (v.2 i)).1) (dim_report v) (fun i=> P.liftOff.lift _ ( RG10.Position.owner (RG10.Position.Deck.token F D (v.2 i))))
local notation "F₁"=> Home.seats P.liftOff P.certified
noncomputable def Story (v:Home.Datum (Glyph U d)): FC:= Perot.cost R B x T (fun i=> (v.2 i).size) (dim_report v) ( fun i=> Home.announcedL (v.2 i) )
lemma stateMean : Story (nativeR P) B x T (U:= Home.seats P.liftOff P.certified) (d:=d) = mix ( Perot.Raw _ _ T P d ) ( readC F F₁ d ):= by
 funext w; rcases w with ⟨y,k⟩; let f(i:Fin y.n):= (k i).size; have hf(i:Fin y.n): f i≤d:= Nat.le_of_lt_succ (k i).1.isLt; let t(n:Fin y.n)(p:Spur F (f n)):=carryΩ F (hf n) (realToken F p)
 symm; rw [monoread (U:=fun n:Fin y.n=> Spur F (f n)) (J:=t)]; rotate_left
 · exact fun i j k h=> eq_of_heq (Sigma.mk.inj h).2
 · intro i k hk; change PowerSeries.C _=0; rw [show Φin _ _ _ _ _=0 from cite_c _ _ _ k (fun ht=>?_ ),map_zero ]; obtain ⟨⟨n,h⟩,u⟩:=k; have hy:n=f i:=congr_arg Prod.fst ht; subst n; exact hk ⟨u,rfl⟩
 let V₁(j:Fin y.n):= announcedL (k j); let u (j:Fin y.n)(i:Spur F (f j)):= Ωc F F₁ ( MS.Land.read (ownCoord (k j)) ) (realToken F i); let w' (j: Fin y.n) (i:Spur F (f j)):= P.liftOff.lift (f j) ( RG10.Position.deck F (f j) (realToken F i))
 change _=Perot.cost (nativeR P) B x T f _ V₁; rw [ funext (fun i=> show V₁ i=∑ j,u i j • w' i j from Eq.symm (Home.off_w P (k i)) ), Perot.priced ]; refine Finset.sum_congr rfl fun v _=>?_ ; unfold Home.readC Φin; simp_rw [ Matrix.map_apply, ← map_prod ]; rw [ mul_comm (PowerSeries.C _) ]; refine congr_arg₂ (· * ·) rfl ?_; apply congr_arg; exact Finset.prod_congr rfl fun i _=> Home.refu F F₁ (k i) _ (v i)
lemma recover : Perot.Raw _ _ T P d= mix (Perot.Story (nativeR P) B x T) (overΩ F F₁ d):=by rw [ stateMean B x T P, mix2, Home.intoC,mix1]

-- real all
variable (hp:∀ n b i v,Home.Profiles.RSpec (T n b i v))
local notation "Pr" => Home.Profiles.RSpec
variable {P}
lemma spend (i: Motor B r x)(D:Fin r→ MS.Rake.Label U):Perot.kernel R (fun i=> (D i).h) (fun i=> popTag (D i)) (T _ i)=Sound.Formal.baseV R D (T _ i):= rfl
include hp
lemma realBase (v:Fin r→Rake.Label U) (i:Motor B r x) : Pr (Perot.kernel R (fun i=>(v i).h) (fun i=>popTag (v i)) (T _ i)):= by
 rw [spend]; apply RSpec.finSum _ _; intro j _; refine (RSpec.mul ?_ (hp _ _ (Rake.Label.h∘v) j));
 let w(k:Fin r):= Lobby.γ R (v k) ( j k ); have h: star (∏ i,w i)= ∏ i,w i:= by rw [star_prod]; exact prod_congr rfl fun i _=> Shop.value_real ..
 let c:=∏ i,w i; change Pr ( C c ); rw [ ← show ( ↑c.re:ℂ )=c from Complex.conj_eq_iff_re.mp h ]; exact RSpec.constants _
lemma realstory (v:Home.Datum (Glyph U d)) : Pr (Story R B x T v):=by
    unfold Story Perot.cost Pegs.compilation; refine RSpec.finSum _ ( fun i _=> (RSpec.constants (Pegs.earn B x _ i)).mul ((RSpec.mul ?_ ( realBase R B x T hp (Lobby.owner ∘ v.2) i ))) ); rw [ ← Complex.ofReal_inv, ← Complex.ofReal_pow ]; exact RSpec.constants _
lemma realraw (P:Plan F)(v:Datum (RG10.Position.Deck F d)): Pr (Raw _ _ T P d v):=by
 rw [recover]; refine RSpec.finSum Finset.univ (fun _ _=> RSpec.mul (realstory (nativeR P) _ _ _ hp _) ?_ )
 · exact RSpec.finProd _ (fun i _=>by rw [Home.θout]; exact RSpec.place _)
-- story high horizon climbing MAT? raw exactly coherent.P.Deck frame proof no interactions.L. 
end YM.RegulatorIR.FVAAlt2.Moving.Perot
