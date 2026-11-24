import YM.Gaps1020.Local.Sales
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Daisy.Charity.RG12

-- query allows *arbitrary fixed* perturbative/Taylor order. All after L.
-- Later take a calendar exhausting every finite K. Pay all geometric and
-- reset-stage operator costs used in RG01 extraction norm at once.
variable (s)
local notation "ROOT" => Trees.degreePrice
local notation "bnd" => horizonRadius G L
structure Receipt {s:ℝ} (Γ:Target.Expense Q) (D : RG.Stage) (M : ℕ) {B v Y d q C' A a r : ℝ}
    {ρ : Cash W s μ L Q o C T R}(N:Captain ρ D.order C' d v Y A a r B q k χ) : Prop where
  plenty : 0 < betaF G s L
  large : 2≤ horizonRadius G L s
  turns : HasClutch N.conduit A
  chargeFits : charge Q L s r D.order (cutLength M s) ≤ (bnd s)⁻¹
  Warn : WarnBudget ((bnd s)^(M+1)) N.conduit
  second : Trees.Ready ρ.smallAt (radiusB s) (fun p=>2^D.order*Thermal1020.total N (cutK M) M (bnd s) ((bnd s)^(M+1)) p) (Γ.earn+Height.asset Γ) (invoice Q L μ s B (bnd s) D.order k (cutK M) M) (Height.asset Γ) (1/2)
  currency : Height.away D*(collars G (Height.asset Γ) s D.order D.power*((invoice Q L μ s B (bnd s) D.order k (cutK M) M)*(1-1/2:ℝ)⁻¹)) ≤ 1

variable {s}
-- Rub predicate
structure ThermalAt (Q:ConnectedActivityE6.Target G P)(Γ:Target.Expense Q) (L:Side) (W μ:ℝ) (ξ:Target.Order G W) (D:RG.Stage) (n:ℕ) (s:ℝ):Prop where
  cost m (_:m≤n) (c f:Side)(S:StepData c f)(T:Tube G S) (hT:Stamp T)(R:Rep G f) (C:ℝ)(U:Cash W s μ L Q ξ C T R):
    ∃ (A a v t d w B q C' :ℝ)(k:ℕ) (N:Captain U D.order C' d v t A a w B q k Chi.canonical), Receipt Γ D m N

lemma decalPresent (Q:ConnectedActivityE6.Target G P)(Γ:Target.Expense Q):∃ n:ℕ,∀ (L:Side), n≤L.val→∀ W μ o D i, Γ.wanting≤-(7/16:ℝ)→0<W→0<μ→∀ᶠ s in atTop,ThermalAt Q Γ L W μ o D i s:=by
  obtain ⟨n,H⟩:= Thermal1020.issued P Q
  refine ⟨n,fun L hL W μ o D i he hW hμ=>?_⟩
  have hh:ray+Q.rate<0:= by unfold ray; linarith [Γ.reach]
  let e:=Height.asset Γ; have ha:0<e:= Height.asset_pos _
  let Ph (m:ℕ) (s:ℝ):Prop:=∀ (c f : Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ (R:Rep G f)(C:ℝ)(U:Cash W s μ L Q o C T R), ∃ (A a v t d w B q C' :ℝ)(k:ℕ) (N:Captain U (D:RG.Stage).order C' d v t A a w B q k Chi.canonical), Receipt Γ D m N
  have ht (m:Fin (i+1)): ∀ᶠ s in atTop, Ph m s:= by
    by_cases hp:∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    swap; · exact Eventually.of_forall fun x c f S T _ R C H=>let h:=H.laws.data.funds; False.elim (hp ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)
    obtain ⟨R,hR,hL',hr⟩:=hp; let k₀:=m.val; let y:= ray*(k₀+1:ℕ)
    obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hJ,hO,hP⟩:= H L hL R hR y (by unfold y ray; positivity) D.order Chi.canonical W hW μ hμ o
    let ρ:= horizonRadius G L; have hx:= revenue Q L μ hμ B hB D.order k₀ k
    have hZ:= (degree10 L _ hx e).below hh (1/2) (by norm_num)
    have hy : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    let c:=fun s=> collars G e s D.order D.power
    have hc: Rate G L 0 c := by simpa only [zero_mul] using! ((hy.pow (D.power*D.order)).mul_right (Reserves.polyPrice e (D.power*D.order)))
    have hp:= (hc.mul (hx.mul_right ((1-1/2:ℝ)⁻¹))).mul_left (Height.away D); rw [zero_add] at hp
    filter_upwards [hP,(Delay.shift_pos G L),radiusLarge L,ready10' Q L μ hμ ρ (b:=ray) Rate.power hh,hZ,hp.below hh 1 zero_lt_one, Thermal1020.compass Q L r hJ hh k₀ D.order] with s hP hs hh hk hΓ hp hS c f S T hT U C' Y
    obtain ⟨N,h₁,h₂⟩:= hP _ _ S T ((Y.laws.data.funds).patch hL' hr) hT U _ Y
    have hD : 1≤ρ s:= by change 2 ≤ ρ s at hh; linarith
    have h : WarnBudget ((ρ s)^(k₀+1)) N.conduit:= by rw [show (ρ s)^(k₀+1)=betaF G s L ^ y from (Real.rpow_mul_natCast hs.le _ _).symm]; exact h₂
    have he: Γ.earn+e+e≤Q.exp := by unfold e Height.asset; linarith
    exact ⟨A,a,v s,t s,d s,r s,B s,q s,C,k,N,⟨hs,hh,h₁,hS,h,Thermal1020.sold N k₀ (cutK k₀) _ h (one_le_pow₀ hD) (zero_lt_one.trans_le hD) hs Γ e ha he hk.1 ((le_abs_self _).trans hΓ), (le_abs_self _).trans hp⟩⟩
  filter_upwards [eventually_all.mpr ht] with s hs
  exact ⟨fun m h c f S T hT U C R=> hs ⟨m,Nat.lt_succ_of_le h⟩ c f S T hT U C R⟩

def vacuum (G:Gauge) : Decal G where
  rub _ Q Γ L W μ o D i s:= ThermalAt Q Γ L W μ o D i s
  good _ Q Γ := decalPresent Q Γ
end YM.ConnectedActivityE6.Blaze.Thermal1020
