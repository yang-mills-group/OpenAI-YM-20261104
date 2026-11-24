import YM.Integration.WilsonThermometerWeakPurseTariff

/-! The enrolled weak reporting purse on its actual Wilson step: independent displaced
slots, full signed product, and the native period-uniform regular and hard rates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalRocket
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open Push.PriceCompiler RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics Tapes Paint
open Thirst Relation Corona Value Glyph Marker Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential Edition
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G)
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

private theorem spatial {n:Side} (W Z:Support n) (subset:W⊆Z) (j:ℕ) (old fresh:BudgetPoint) (y e γ:ℝ) (hy:0≤y) (he:0≤e) :
    debt fresh.B e W≤debt fresh.B e Z ∧ strand W j old fresh y e γ≤ strand Z j old fresh y e γ:=by
  have monotone {S T:Support n} (h:S⊆T) {z:ℝ} (hz:0≤z):debt fresh.B z S≤debt fresh.B z T:=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast cover_mono h fresh.B) hz)
  refine ⟨monotone subset he,?_⟩
  unfold strand Edition.debit
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (wilty _)
  exact mul_le_mul_of_nonneg_left (monotone (halo_mono le_rfl subset) (by linarith:0≤e+2)) (by positivity)

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G)
    (d D:ℕ) (hd:d≤D):
    ∀ᶠ k:ℕ in atTop,∀ N (_:k≤N) p (ξ:Purse) (b:ℝ) (menu:Launch Rf k ξ (-3) b)
      (Q:Rep G ((Rf).side k p)),survivors Rf N k p menu.pane Q → ξ.taylor=D → 8≤ξ.era.coast.Q →
    let P:=(Rf).path.rep N p k;let s:=clim (Lev) k;let Z:=Spindle.patch (sizeQ Rf k) (0:Site ((Rf).side k p))
    let F:=(Rf).labels.level d;let g:=GaugeScale Rf k N p;let w:=bill ξ.f s
    ∀ (V:Type) [Fintype V] [DecidableEq V] (ζ:V→Site ((Rf).side k p)) (zs:V→Signed) (a:V→Prop),
    Spaced P.p.B ζ → ∀ (K:(j:V)→Provision Rf d k N p (scouts Rf k) (sizeQ Rf k))
      (X:V→ Coefficient F ((Rf).side k p)) (L:V→poly (Up Rf k p (sizeQ Rf k)))
      (y:V→Palette Rf d) (fmt:∀ j,(X j).Format 0 (Rf).params P),
    let W:=fun j=>sender (K j).length P.p.threshold g (L j)
    (∀ j,(X j).remBound 0 P (kappa (Rf).path k) (B d k*size (y j))) →
    (∀ j,Germ.projection F (Rf).params P.p.threshold 0 (X j)=(y j) (primaryLetter d)) →
    (∀ j,size (y j)≤bill (ξ.credit-1) s) → (∀ j,Spirit (W j)) →
    (∀ j U,Healthy (tau (Lev) k) Z U→‖(X j).exponentialEntry 0 ((Rf).localSection d) P U-signet 0 g (W j) U‖≤
        bill (1/8-(D:ℝ)) s*size (y j)) →
    ∀ (vac:Neat ((Rf).side k p)→Burst G ((Rf).side k p) P.p.threshold),IsoVac P vac ((Lev).clock.forcedAllowance k) →
    ∀ (ι κ:Type) [Fintype ι] [Fintype κ] (reg:ι→SourceAt G ζ) (hard:κ→Lifted G ζ P.p.threshold),
    Unpacks reg P.p (fun _=>Hat s^b) P.p.supportExponent 1 → Unfold (p:=P.p) hard (fun _=>Hat s^b) P.p.supportExponent 1 →
    (∀ j,2≤(reg j).fires.val.card) → (∀ j,2≤(hard j).fires.val.card) →
    ∃ (α β:Type),∃ (_:Fintype α) (_:Fintype β),∃ (file:V→SourceAt G ζ) (ordinary:α→SourceAt G ζ) (forced:β→Lifted G ζ Q.p.threshold),
    (∀ j,(file j).extent=swath (zs j) (ζ j) Z ∧ (file j).fires=slot j ∧
      (file j).value=dot (a j) ∘ signet 0 g (W j) ∘ pull (zs j) (ζ j)) ∧
    credsX ζ (fun _=>(Rf).localSection d) X fmt zs a vac (fun _=>1) hard reg=dust Q (Sum.elim ordinary file) forced ∧
    Background Q forced ∧ Unpacks ordinary Q.p (fun _=>w) (load ξ.era) (bill (-(ξ.goal:ℝ)) s) ∧
    Alarm.prepared (q:=Q.p) forced (fun _=>w) (load ξ.era) (Real.exp (-(trib ξ.era.coast.a s))) :=by
  filter_upwards [WilsonThermometerWeakOriginalShelves.purchased R simple d D hd S,
    WilsonThermometerWeakPurseTariff.original R simple shop d] with k shelf purse N hk p ξ b menu Q received Taylor room P s Z F g w V _ _ ζ zs a separate K X L y fmt W rem germ credit spin fitted vac vacuum ι κ _ _ reg hard regularStock compulsory reg2 hard2
  obtain ⟨_,_,sig,W',mapped,drama,price,_,_⟩:=received
  let q:=inbox Rf k menu.pane;let e:=load ξ.era;let u:=trib ξ.era.coast.a s
  have equal:Q.p=q:=mapped.precise.2.2.2.2.1
  have pbeta:Q.beta=P.beta:=mapped.precise.2.2.2.2.2.1
  have stage:P.p=(Lev).budget k:=(R.makes.wilson.represents N p k hk).vac
  have width:Q.p.B=walls s:=equal ▸ rfl
  have θ:Q.p.threshold=tau (Lev) k:=equal ▸ rfl
  have low:Lower P.p Q.p:=equal ▸ drama.squeeze.1
  have bridge:∃ (S':Siren G ((Rf).side k p) Q.p.threshold) (Ω:ValidX ((Rf).side k p)→Wickless G _ Q.p.threshold),
      Bridges P Q e u (((Lev).params k).width) (((Lev).params k).paths) ((Lev).clock.loopCap k) (delta s) S' Ω (q:=Q.p):=by
    rw [equal];exact ⟨sig,W',mapped⟩
  obtain ⟨S',Ω,turn⟩:=bridge
  have order:D+1≤P.p.order:=by rw [stage,←Taylor];exact menu.length
  have orig:P.p.B=M s:=stage▸rfl
  have aperture:P.p.threshold=regular s:=stage ▸ (historic (Lev) k).1
  let filed:=fun j=>bill (1/8-(D:ℝ)) s*size (y j)
  have filed0 j:0≤filed j:=mul_nonneg (Real.exp_pos _).le (size_ge _)
  choose file error forced far xFile fFile valFile xError fError xForce fForce sf pay costs using
    fun j:V=>shelf N hk p (K j) (X j) (L j) order (fmt j) (rem j) (filed0 j) (spin j) (fitted j) Q.p θ low V ζ (zs j) (a j) j
  have cash j:=purse N p hk (X j) (y j) ξ D (filed j) (fmt j) (rem j) (germ j) (credit j) le_rfl
  have hw:0<w:=Real.exp_pos _
  have e0:0≤e:=q.exponent_pos.le.trans drama.wide
  let shift:=garn ξ.goal s
  have rent:=menu.grant
  obtain ⟨⟨rebate⟩,scale,book⟩:=rent.2 P.p Q.p orig width aperture (stage▸rfl) low
  let large:Keepat ((Rf).side k p):=⟨halo (ξ.era.coast.Q*Q.p.B) {0},halo_subset _ _ (Finset.mem_singleton_self _)⟩
  obtain ⟨regularRate,forcedRate,geometry,positive⟩:=book _ large rfl
  have inclusion:Z⊆large.val:=by apply halo_mono _ (le_refl _);change 8*walls s≤ξ.era.coast.Q*Q.p.B;rw [width];exact Nat.mul_le_mul_right _ room
  have weak:=spatial Z large.val inclusion (scouts Rf k) P.p Q.p (bill (-8) s) e shift (Real.exp_pos _).le e0
  have cells j:=costs j (fun _=>w) hw.le
  have behind:(Lev).clock.forcedAllowance k=forcing s:=by unfold Calendar.forcedAllowance; rw [(historic (Lev) k).2.2];rfl
  have cascade:2*vacancies e ((Lev).clock.loopCap k) (((Lev).params k).width) (((Lev).params k).paths) (delta s) P.beta P.p Q.p+
      strand Z (scouts Rf k) P.p Q.p (bill (-8) s) e shift+mech ((Lev).clock.forcedAllowance k) Q.p (bill (-8) s) e shift+
      batch u (e+1) Q.p.B≤bill (-1) s:=by
    rw [behind];apply le_trans _ forcedRate;apply add_le_add _ le_rfl;apply add_le_add _ le_rfl
    exact add_le_add (mul_le_mul_of_nonneg_left (by rw [pbeta] at price;rw [equal];exact price) (by norm_num)) weak.2
  have rpos:0<Hat s:=by rw [logged _ menu.pane.provision.1];positivity
  obtain ⟨same,bkg,un,alarm⟩:=WilsonThermometerWeakOriginalPrepared.delivered
    (fun _=>(Rf).localSection d) X fmt zs a vac hard reg file error forced far Z (scouts Rf k)
    low separate hw drama.cost e0 (Real.rpow_pos_of_pos rpos _) (Real.exp_pos _).le (Real.exp_pos _).le
    rebate scale S' Ω turn vacuum (fun j=>B d k*size (y j)) rem (fun j=>(cash j).1)
    regularStock compulsory reg2 hard2 xError fError xForce fForce (fun j h=>(sf j h).2) pay
    (fun j=>⟨(cells j).1.1.trans (cash j).2.2,fun U hU=>(cells j).1.2 U hU |>.trans (cash j).2.2⟩)
    (fun j=>⟨(cells j).2.1.1.trans (cash j).2.1,fun U=>((cells j).2.1.2 U).trans (cash j).2.1⟩)
    (fun j=>by
      obtain ⟨f,hp,price⟩:=(cells j).2.2 (e+2) (by linarith) scale
      exact ⟨f,hp,price.trans (mul_le_mul_of_nonneg_left (cash j).1 (by positivity))⟩)
    cascade geometry
  refine ⟨_,_,inferInstance,inferInstance,file,_,_,fun j=>⟨xFile j,fFile j,valFile j⟩,same,bkg,un.relax ?_,?_⟩
  · rw [←Taylor];apply le_trans _ regularRate;exact add_le_add (mul_le_mul_of_nonneg_left weak.1 (Real.exp_pos _).le) le_rfl
  · obtain ⟨m,h,hm⟩:=alarm
    refine ⟨m,h,fun j=>?_⟩
    exact ⟨(hm j).1,(hm j).2.1,(hm j).2.2.trans (mul_le_of_le_one_right (Real.exp_pos _).le positive)⟩

end YM.Integration.WilsonThermometerWeakOriginalRocket
end
