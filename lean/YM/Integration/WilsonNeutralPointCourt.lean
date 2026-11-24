import YM.Integration.WilsonNeutralPointMatrix
import YM.FormalBulk08.Firth.Left
import YM.FormalBulk08.Roof.Enroll

/-! A selected single child lands in the same class of full normalized
fields at the next date.  The incoming test and all angular coefficients
belong to one finite conditional law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralPointCourt
open FormalBulk08
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision Tree
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Sierra Firth
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{j t D l u d:ℕ}{K:KernelChoices}
variable (o:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(Y:Anthem D G)(ρ:ChartRatio G)
    (h:P.patch.Branches K G)(hL:2≤P.L.val)(x:Site P.L)

def raw (rank:ℕ):Anthem D G:=fun f=>braise P V W (stepsong P Y hL f x) ρ h rank

/-- The original absolute component sum at the chosen child. -/
theorem wages (hp:Wade o Y l)(hv:Story W (pink K.penalty P.wing))(hr:LocalRatio ρ)
    (ht:4≤t)(u:ℕ)(e r:ℕ):∃ η:ℝ,0<η ∧
      LightPay (fame _) η (0,o) (fun p=>raw P V W Y ρ h hL x u p e r) (‖·‖):=by
    let k n:=Classical.choice (chooseable n (n*P.patch.L) (primary P.patch K n))
    obtain ⟨θ,hθ,hf,hU⟩:= wedge_step o P Y W hp hv hL e
    obtain ⟨s,C,hs,hC,hA⟩:=aone P (K:=K) G ht
    obtain ⟨z,B,hz,hB⟩:=(gamma_ready G K P V h).1
    let η:=min (min s z) (P.L.val*θ)
    have hη:0<η:=by unfold η;positivity
    have hT:=show (Flight.duo K.penalty P).A0.strip η C from
      strip_mono hA ((min_le_left ..).trans (min_le_left ..)) le_rfl
    let c:ℝ:=max 0 B
    have hc:0≤c:=le_max_left ..
    let q:=lands (rayshot P V h)
    have Q:(gamma G K P V h).strip η c:=strip_mono hB ((min_le_left ..).trans (min_le_right ..)) (le_max_right ..)
    have hh:η≤P.L.val*θ:=min_le_right ..
    let X:=coastRight Cover (Minor G P.patch V) (Loc G 1) (0,o)
    obtain ⟨H,hS⟩:=ray_cover P V h hη.le hc Q
    refine ⟨η,hη,?_⟩
    unfold raw braise
    apply pay_sums;intro i _hi
    have sectionBill: LightPay (fame _) η X (fun p=>border P V W (stepsong P Y hL p x) ρ h i e r) (‖·‖):=by
      apply light_income (o:=X) e i q (magma P V W ρ h) (fun p=>coves K P V (stepsong P Y hL p x))
        hη.le (H.turn hS) _ _ e le_rfl r
      · intro i b _ hb r l
        obtain ⟨hp,C,H⟩:=redskin P V W ρ h k hη hC hh hT hc Q hv.toVivid hr i b r (⟨0,l⟩:Fin r)
          (fun j hj r=>hf j (hj.trans hb) r)
        exact ⟨C,lit_width hp C H⟩
      · intro j hj r
        obtain ⟨B,hB,H⟩:=hU j hj r
        let site:=scroll P.patch.L (Loc G 1) (lift x,o)
        obtain ⟨A,_,hv⟩:=Lodge.bothPay G K V η hη
        have hM:(locating G K P V).strip η (A*C):=(hv _ _ hC hT).1
        let d:=Fintype.card (Board G P.patch)
        let d':=Fintype.card (BoardL G P.patch V)
        let g:ℝ:=max 1 (A*C)
        have hg:0≤g:=le_trans zero_le_one (le_max_left ..)
        let v:ℝ:=Real.exp (8*η)*B*(d:ℝ)^r*(d':ℝ)^r*((d':ℝ)*g)^r
        refine ⟨v,by unfold v;positivity,fun p=>?_⟩
        have hz:Knoxville (fame _) θ ((scroll P.patch.L (Loc G 1)).symm site) _ _:=
          (scroll P.patch.L (Loc G 1)).symm_apply_apply (lift x,o) |>.symm ▸ H p x
        have fine:=rinse_bill _ _ hh hη.le _ hz
        have wing:=penn_pearl (winging (Bank.Rim G P.patch) (Loc G 1)) _ (Sum.inr o)
          fine hη.le (wing_strip η) zero_le_one
        have paneFee:=penn_pearl (pane G P.patch V) _ (Sum.inr o) wing hη.le (pane_pay V _) zero_le_one
        have placed:=penn_pearl (zealand K P V G) _ (Sum.inr o) paneFee hη.le (zealandPay K P V hM) hg
        unfold X;rw [←chief_h o P x];apply Knoxville.mono placed
        apply le_of_eq;unfold v
        change 1*(1*(1*(_*((d:ℝ)*1)^r)*((d':ℝ)*1)^r)*((d':ℝ)*g)^r)=_
        ring
    obtain ⟨B,hB,earned⟩:=sectionBill;exact ⟨B,hB,fun p=>penn_port (earned p)⟩

theorem original (a:hue G)(hy:Clef o Y l)(hv:Story W (pink K.penalty P.wing))(hr:LocalRatio ρ)
    (ht:4≤t)(u d:ℕ)(cap:l≤u):
    Clef o (WilsonNeutralPointMatrix.child P V W a ρ h hL d u x Y) l:=by
  let inside (f:Studio D):=stepsong P Y hL f x
  have paid (f:Studio D):Ritual (inside f) l:=from_R _ l (ritual_cell o _ hy) (lift x)
  let f₀:=raw P V W Y ρ h hL x l
  have full (f:Studio D):Ritual (f₀ f) l:=
    paragon (0,o) P V W ρ h hv hr ht (paid f) (fun n=>Classical.choice (chooseable n _ (primary P.patch K n)))
  have c:Clef o f₀ l:=by
    refine ⟨⟨?_,?_⟩,⟨fun f=>(full f).young,fun f=>(full f).committees,?_⟩,
        (solo_iff f₀).mpr fun n f=>(full f).esteem n⟩
    · intro f g
      have upper:inside (f+g)=inside f+inside g:=by unfold inside stepsong;rw [map_add,hy.map_add];rfl
      change braise P V W (inside (f+g)) ρ h l=_
      rw [upper];exact plusT a P V h hr hv ht (paid f) (paid g)
    · intro b f
      have upper:inside (b • f)=b • inside f:=by unfold inside stepsong;rw [map_smul,hy.map_smul];rfl
      change braise P V W (inside (b • f)) ρ h l=_
      rw [upper];exact dime a P V h hr hv ht (paid f) b
    · intro e r
      obtain ⟨η,positive,C,nonneg,H⟩:=wages o P V W Y ρ h hL x hy.fare hv hr ht l e r
      exact ⟨η,C,positive,nonneg,H⟩
  let E:=epoch a P V K W ρ h
  have reset:Clef o (((P.L.val:ℝ)^d) • stir (bookH E) (bookU E) f₀) l:=
    (c.stirs (book_equal E)).smul _
  convert reset using 1
  funext f
  change (P.L.val:ℝ)^d • stamp (bookH E) (bookU E) (braise P V W (inside f) ρ h u)=_
  rw [cap_braise P V ρ h hr hv.toVivid _ (paid f).young u cap]
  rfl

end YM.Integration.WilsonNeutralPointCourt
end
