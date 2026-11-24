import YM.Integration.WilsonNeutralPointCourse
import YM.Integration.WilsonNeutralObservedCover
import YM.Integration.FVA1Physical.TwoReset.Copies

/-! The actual copied packet at any one fine site is averaged over its
original pages before returning the normalized finite reading. The
conditional and full unmarked action stay common to all fine copies. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointPageAverage
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open Work.F03 Work.F05 Work.F08
open scoped Topology BigOperators Matrix Classical ContDiff Matrix.Norms.Frobenius

section Shift
variable {G:Gauge}{p:Side}(x:Site p)
private lemma relocated (Z:Pap (wire G p))(h:Rite Z Z 1 0):Rite (resite x Z) Z 1 x:= by
   intro I y a b k ha hb hP hT hA hG hx; rw [label_w x a ha hP Z];
   apply h I (fun z=> a z ∘ Lotus.tint x) b k (by rw [ha];rfl) hb (contDiffAt_pi.mpr fun j=>contDiffAt_pi.mp hP (Lotus.tint x j)) hT hA hG; filter_upwards [hx] with z hz;rw [pull_id,zooms,hz]
private lemma recovered (Z Y:Pap (wire G p))(h:Rite Z Y 1 x): Z=resite x Y:= by
    let T:=fun a:Jets.Rays (wire G p)=> a ∘ Lotus.tint x
    have hx: ContDiffAt ℝ ω T 0:=contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    obtain H:= h (wire G p) (fun y=> y ∘ (id : wire G p→_)) T 1 rfl rfl (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) hx (fun _=>contDiffAt_const) ⟨1,rfl⟩ (.of_forall fun z=>by funext u; simp [T,zooms,Lattice.gauge]); rw [fit_translate, show T=(fun a: Jets.Rays (wire G p)=> a∘ Lotus.tint x) from rfl,fit_translate] at H; convert H using 1; ext1 n;simp
    rfl
end Shift

private theorem placed_sum {G:Gauge}{p:Side}(x y:Site p)(Z:Pap (wire G p)):
    resite (x+y) Z=resite x (resite y Z):=by
  ext1 e
  rw [resite,resite,resite,coeff_map,coeff_map,coeff_map]
  change MvPolynomial.rename _ (coeff e Z)=MvPolynomial.rename _ (MvPolynomial.rename _ (coeff e Z))
  rw [MvPolynomial.rename_rename]
  apply congrArg (fun g:wire G p→wire G p=>MvPolynomial.rename g (coeff e Z))
  funext u;apply Prod.ext (by change u.1+(x+y)=(u.1+y)+x; abel) (by rfl)

private theorem reference {G:Gauge}{n N:Side}(h:n.val∣N.val)(x:Site N)
    (B:wire G n→ℝ)(p:Pap (wire G N))(e:ℕ):
    MvPolynomial.eval (B ∘ Prod.map (splitter h) id) (coeff e (resite x p))=
    MvPolynomial.eval (B ∘ Lotus.tint (splitter h x) ∘ Prod.map (splitter h) id) (coeff e p):=by
  rw [resite,coeff_map]
  change MvPolynomial.eval _ (MvPolynomial.rename _ (coeff e p))=_
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun g:wire G N→ℝ=>MvPolynomial.eval g (coeff e p))
  funext u;apply congrArg B
  exact Prod.ext (map_add (splitter h) u.1 x) rfl

variable {G:Gauge}{d D:ℕ}(R:Run G)(wood:Primer.Families R.family)(a:hue G)
variable (depth:d<D)(digit:∀i,Site (R.family.S.block i)){U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)

include grant in
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n M:Side)(h:n.val∣M.val)(b:Letter (R.family.labels.level d))(f:Studio D)
    (z:Site (n*(destination R.family.path.levels N i).L))
    (t:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel M).Choices)
    (B:wire G n→ℝ)(e:ℕ):
    let A:=destination R.family.path.levels N i
    let r:Ratio n (n*A.L):=Ratio.mk A.L rfl
    let R':Ratio M (M*A.L):=Ratio.mk A.L rfl
    let fine_dvd: (n*A.L).val∣(M*A.L).val:=subdiv_dvd r R' rfl h
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let Z:=banner d (WilsonNeutralPointCourse.filed R wood a depth digit N (i+1) b f) (M*A.L)
    let Q:=tossed A R.metals.O (R.family.path.levels.blocks i 0).branches (wood i) M t (stone w (M*A.L))
    let E:=fun (p:Site (M*A.L))=>MvPolynomial.eval (B∘Prod.map (splitter h) id) (coeff e (Q (resite p Z)))
    let V:=MvPolynomial.eval (B ∘ Lotus.tint (r.parent z) ∘ Prod.map (splitter h) id)
      (coeff e (Q (resite (wrap (M*A.L) (lift (r.residue z))) Z)))
    (Pages (n*A.L) (M*A.L):ℝ)⁻¹*(∑ u:Fin (Pages (n*A.L) (M*A.L)),E (page fine_dvd z u).val)=V:=by
  intro A r R' fine_dvd w Z Q E V
  have c:=WilsonNeutralPointCourse.original R wood a depth digit N (i+1) hs o live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have lawful:Rite Z Z 1 0:=by
    dsimp only [Z]
    exact (solo_iff ..).mp (clef_through (c.officers b) (slotsFits _ b)).ward (M*A.L) f
  have state:=Dove.genu R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
    R.alloy.B.ratio hs (i:=i+1) (N:=N) live
  obtain ⟨sym,C,h0,hC,stock,-⟩:=colors G R.family.path.levels.clock.kernel.penalty
    R.family.path.levels.clock.kernel.penalty_pos A.legal
  have head:=stoned_main h0.le hC.le (stock A.wing).1 state.toVivid state.ink (M*A.L)
  let k:=wrap (M*A.L) (lift (r.residue z))
  have tap:Rite (resite k Z) (resite k Z) 1 0:=by
    simpa only [Signed.act_one] using! (Kemp.repulp (x:=k) 1 Z Z lawful)
  have slide (y:Site M):Q (resite (R'.assemble (y,r.residue z)) Z)=resite y (Q (resite k Z)):=by
    change Q (resite (R'.embed y+k) Z)=_
    refine (congrArg Q (placed_sum (R'.embed y) k Z)).trans ?_
    apply recovered
    dsimp only [Q,w]
    rw [←WilsonNeutralAppointedForestStep.vacuum R wood a grant]
    exact Reef.tossed_ward A R.metals.O (R.family.path.levels.blocks i 0).branches (wood i) M t _
      head R.alloy.B.ratio (R.family.path.levels.clock.adm i) (state.civic _) 1 y _ _ (relocated _ _ tap)
  have same (u:Fin (Pages (n*A.L) (M*A.L))) : E (page fine_dvd z u).val=V:=by
    have entry: (page fine_dvd z u).val∈parcel (splitter fine_dvd) z:=(page fine_dvd z u).property
    have inside:=(subdiv_marks (ℓ:=A.L) rfl rfl h fine_dvd z).le entry
    obtain ⟨y,hy,atPage⟩:=Finset.mem_image.mp inside
    rw [←atPage]
    change MvPolynomial.eval _ (coeff e (Q (resite (R'.assemble (y,r.residue z)) Z)))=_
    rw [slide,reference]
    have anchor:splitter h y=r.parent z:=(Shingle.posted ..).mp hy
    dsimp only [V]
    rw [anchor]
  simp_rw [same]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have positive:0<Pages (n*A.L) (M*A.L):=pow_pos (Nat.div_pos
    (Nat.le_of_dvd (M*A.L).pos fine_dvd) (n*A.L).pos) _
  field_simp [show (Pages (n*A.L) (M*A.L):ℝ)≠0 by exact_mod_cast positive.ne']

end YM.Integration.WilsonNeutralPointPageAverage
end
