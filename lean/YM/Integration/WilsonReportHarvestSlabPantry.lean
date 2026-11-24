import YM.RG05Readout.Capture.Fronds

/-! Group a genuine earlier reference with the law and the currency of its
actual Wilson date. No microscopic boundary condition is needed at capture. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabPantry
open RG05Readout RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.Fibers Ribbons.ManyCopies
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {n m p N d b k:ℕ} {V W:Type} [DecidableEq W] [Fintype W]
    [DecidableEq V] [Fintype V] {D:Address.Rail C} {Y:Census (Unit×W)} {Z:Census (Unit×V)} {Q:ℝ}
set_option quotPrecheck false
local notation "S0" => C.path.levels
local notation "K" => C.path.levels.clock
local notation "X" => C.path
local notation "Ζ" => C.path.levels.budget
local notation "u" => Legato.Bandage.renal C.path.levels
local notation "t" => (Ζ n).supportExponent
local notation "P₀" => C.path.rep N p n
local notation "Z0" => apron C.path.levels
local notation "l!" => Ribbons.peepers C.path.levels n
local notation "ζ" => fee C m n d k b Q
local notation "σ" => crust C m n d k Q

theorem original (hC:C.Makes) (heC:Cater C D) (o:Unit×W→Site (C.side n p))
    (T:Ribbons.Fibers W V) (U:Unit×W→ℂ) {rows:Unit×W→Three G (C.side n p)}
    {A:Config G (C.side n p)→Poly Y} (hn:0<n) (nN:n≤N)
    (ho:Occupancy o ((K).J n)) (hσ:0<σ) (hp':Integrable A (prior G _))
    {b':ℝ} (hZ:Furls S0 n b') (hA:Alcove P₀ rows A o (fun _=>σ) b' (u n) (1/2))
    (hh:∀i,‖U i‖≤1) (hf:0<b) (hb:∀i:Unit×V,((Ribbons.ManyCopies.partialGroup Unit T).contents i).card≤b)
    (s':Finset V) (ha:∀i∈s',T.Solo i) (hT:Pantry.Policy T Y Z)
    (h_l:∀i:Unit×W,coverNumber (Ζ n).B ({(o ∘ (Ribbons.ManyCopies.partialGroup Unit T).twig)
      ((Ribbons.ManyCopies.partialGroup Unit T).bunch i),o i}:Support (C.side n p))≤l!) :
    0<ζ ∧ ∃X':Unit×V→Three G (C.side n p),
      MenuBoard P₀ X' (fun U'=>Pantry.pilot T hT (spice Y U A U'))
        (o∘(Ribbons.ManyCopies.partialGroup Unit T).twig) (fun _=>ζ) (t-2) 1 ∧
      ∀i:Unit×V, let x:=(Ribbons.ManyCopies.partialGroup Unit T).twig i
        (i.2∈s'→X' i=stuff (rows x) P₀ (U x)) ∧
        (i.2∉s'→MergeProof.Float.Blade P₀ (o x) ((X' i).snd.1)
          (profile (P₀).activities ((X' i).snd.2)) 0 (4*(1/ζ))) := by
    have hhX:=hC.wilson.represents N p n nN
    let a:=u n
    let C₀:=P₀
    let D':=Ribbons.ManyCopies.partialGroup Unit T
    have hΨ : Arsenal C₀:=by
       cases n with
       | zero=> omega
       | succ n=> obtain ⟨z,y,hC,-⟩:= heC.tiers n N p (Nat.lt_of_succ_le nN); exact hC.publishes.contact
    have hs : C₀.p=Ζ n:=hhX.vac; obtain ⟨hg,hY,hV,hN,h,Hq,hS'⟩:=hZ.eye
    let N':= syrup C m n d k b Q; have he:0 < N':=by unfold N' syrup Fibers.Salt.tow; positivity
    have hb' : N'≤1:= by
       have hs':a/(b:ℝ) ≤ 1:=(div_le_self (show 0 ≤ a from hY.le) (show 1 ≤ (b:ℝ) from Nat.one_le_cast.mpr hf)).trans hV
       apply le_trans (div_le_self (show 0 ≤ a/(b:ℝ)*σ from by have h:0<a:=hY; positivity) (Real.one_le_exp (mul_nonneg (by change 0≤ t +1/2; linarith only [hN]) (Nat.cast_nonneg _)))) (mul_le_one₀ hs' hσ.le ((show σ ≤ 1/2 from min_le_left ..).trans (by norm_num)))
    have hv (i:Unit×W): (σ)*‖U i‖ ≤ 1/2:= (mul_le_of_le_one_right hσ.le (hh _)).trans (min_le_left ..)
    let U₀:=fun i:Unit×W=>stuff (rows i) C₀ (U i); let f:= spice Y U A; have hB0 : Alcove C₀ U₀ f o (fun _=>σ) b' a 1:= (show (1:ℝ)/2+1/2=1 from by ring) ▸ hA.spiced U hv (fun _=>hσ.le)
    let r'(j:Unit×V):= ∏ _i∈ D'.contents j,N'; let S'(j:Unit×V):= ∏ i∈ D'.contents j,Fibers.Salt.tow (fun _=>σ) (C₀.p.supportExponent+1/2) (a/b) (l!) i
    have hg'(i): ζ ≤ S' i:=by
         change N'^b ≤ _; have hr: S' i= N'^(D'.contents i).card:=by unfold N' S' syrup; rw [hs]; exact Finset.prod_const _
         rw [hr]; exact pow_le_pow_of_le_one he.le hb' (hb i)
    have hoP: Occupancy o (Z0 n):= fun i=> (ho i).trans (((S0|>.fits.mono n.le_succ).trans (Nat.le_add_right ..)).trans (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block n).property _)))
    have hXk: Occupancy (o ∘ D'.twig) (Z0 n):=by
       intro i; let B':=Finset.univ.filter (fun j:Unit×V=> o (D'.twig j)=i); let L:=Finset.univ.filter fun j:Unit×W=> o j=i
       apply le_trans (le_of_eq (Finset.card_image_of_injOn (s:=B') D'.sectioned.injective.injOn).symm) (le_trans (b:=L.card) _ _)
       · refine Finset.card_le_card ?_; intro j hj; obtain ⟨j,hJ,rfl⟩:=Finset.mem_image.mp hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hJ).2⟩
       exact (ho i).trans (((S0|>.fits.mono n.le_succ).trans (Nat.le_add_right ..)).trans (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block n).property _)))
    obtain ⟨Q',hL,hΩ⟩:=Pantry.breakfast (o:=o) T hT hf hb hB0 hhX.good.labels hΨ (hs.symm ▸ (show 2 ≤ t by linarith only [hN])) ha (fun _=>hσ) hg hY hV (N:=Z0 n) hoP hXk (hs.symm ▸ h_l) (hs.symm ▸ h) (hs.symm ▸ Hq) (hs.symm ▸ hS') (fun i=> (Tour.bright (X) ‹C.Makes›.wilson N p n nN i).ne') (spice_live U hp')
    · have hξ:0< ζ:=pow_pos he _; refine ⟨hξ,Q',⟨hL.cleared,hL.fettled,?_⟩,fun i=> ⟨(hΩ i).1,fun hi=>?_⟩⟩
      · have hc:=hL.grants; let Xk:=C₀.p.supportExponent-2; have ht': 1*(1:ℝ)≤1:=by norm_num
        apply hc.prune _ _ (slighter _ _ (w:=1) _ zero_le_one le_rfl) zero_le_one (show t-2+0 ≤ C₀.p.supportExponent-2 from by rw [add_zero,hs]) ht'; all_goals intros i; first | exact hξ| exact hξ.trans_le (hg' i) | exact (hg' i).trans_eq (one_mul _).symm
      exact ((hΩ i).2 hi).more (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hξ (hg' i)) (by norm_num))
end YM.Integration.WilsonReportHarvestSlabPantry
