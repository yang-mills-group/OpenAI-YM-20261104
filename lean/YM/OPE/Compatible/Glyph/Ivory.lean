import YM.OPE.Compatible.Glyph.Truce
/-!
# Root story. Uses finite measure gauge. All bridges on cofinal tori of ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Exterior WithLp Work.F08 Matrix Bloch Precision Stationary
open scoped Topology BigOperators Classical
variable {G:Gauge} {B:Sponsor G}{H: Seasons B}{i j:ℕ}{Λ U D:ℝ}{W: ChartRatio G}
-- switch
structure Charm (L:Side) (M: Alps B H i Λ)(N: Alps B H j U)(b:ℝ)(T: ChartRatio G) : Prop where
   mag : Mag i j
   ink : ∃ P:Flight i j,P.L=L∧ M.gear=P.wing∧N.gear=P.land ∧ Pilgrim G P B.K M.clip N.clip M.live N.live b T
abbrev big_cost (u:Quota B H i j)(L: Side):ℝ:= u.tariff +|G.slopeConstant *Real.log (L.val:ℝ)|
lemma tuber {c:Clip}(hc:c.direct≤ B.γ j)(L:Side)(u:Quota B H i j)(h:u.minL ≤ L.val)(hh:3 ≤ L.val)(he:u.tab L ≤ D)(hv: Mag i j)(ho:Odd L.val)(hy:LocalRatio W)(hZ: 1≤Λ)(hw:Λ/2≤D)(M:Alps B H i Λ): ∃ N:Alps B H j D,∃ b, |b| ≤ big_cost u L ∧ N.clip=c∧Charm L M N b W:=by
    let P:Flight i j:=⟨L,ho,hh,hv.1,by obtain ⟨_,_,h⟩:= hv; omega,by obtain ⟨_,_,h⟩:= hv; omega,M.gear⟩; obtain ⟨X,Hx⟩:= atBed B _ hc hv.2.1 P.land; obtain ⟨b,Y,hb,hT,hY,K⟩:=handstone B P _ _ M.live M.active Hx hv u.admits u.opens M.fills M.pays hZ h _ hy
    exact ⟨⟨c,P.land,X,Y,Hx,hY,K _ _ _ (H.positive j) u.wind u.grip he hw⟩, b, driving_abs _ _ _ hb,rfl, hv,P,rfl,rfl,rfl,hT⟩
-- recurrence α at virtual
abbrev Hatch (A:Quota B H i j)(L:Side)(x:ℝ):= max (max 1 (A.tab L)) x -- sometimes not halving
lemma drum (u:Quota B H i i) {L:Side}(c:Clip)(hp:c.direct≤ B.γ i)(hx:u.minL ≤ L.val)(hz: u.tab L≤Λ)(hy:Mag i i)(hg: 3 ≤ L.val)(hr:Odd L.val)(hn:1 ≤ Λ)(hW:LocalRatio W)(p:Alps B H i Λ): ∃ V:ℕ→ Alps B H i Λ,∃ f:ℕ→ℝ,V 0=p ∧ ∀ n:ℕ, |f n|≤big_cost u L ∧ (V (n+1)).clip=c∧Charm L (V n) (V (n+1)) (f n) W:=by
    choose a v hf using tuber hp L u hx hg hz hy hr hW hn (show Λ/2≤ Λ by linarith) -- need n forall
    let V(n:ℕ): Alps B H i Λ:= Nat.rec p (fun _ v=>a v) n
    exact ⟨V,fun i=>v (V i),rfl,fun n=>hf (V n)⟩
end YM.OPE.Votive
