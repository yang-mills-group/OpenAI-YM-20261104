import YangMills.WilsonProof.NativeSupport.PacketTracks
import YM.FullVolume.Cross

/-! A finite, period-independent error estimate on the original selected
run. The physical factors may be arbitrarily far from each other. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories RGComparison.Core16 RGGapR2
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge}

def seedRadius (R : Run G) (N s : ℕ) : ℝ :=
  Bandage.far R.alloy.B.a N*Real.exp (-((R.alloy.B.a.budget N).supportExponent+1)*(2*(s:ℝ)+1)^4)

def nativeRadius (R : Run G) (k N s : ℕ) : ℝ :=
  corridorRadius (Bandage.renal R.alloy.B.a) k N (seedRadius R N s)

def logLoss (R : Run G) (k N s : ℕ) := max 0 (-Real.log (nativeRadius R k N s))
def spacing (M L : ℕ) := 2*M+4*(2*M+1)*L
def charge (m R : ℕ) := 1+m^2*(2*R+1)^4

private theorem positive_seed (R : Run G) (N s : ℕ) : 0<seedRadius R N s := by
  have hb := zero_lt_one.trans (R.alloy.B.a.fits.delayed N)
  apply mul_pos _ (Real.exp_pos _)
  change 0<(Real.sqrt (R.alloy.B.a.clock.hatBeta N))⁻¹/4
  positivity

private theorem pays_radius (R : Run G) (k N s : ℕ) :
    Real.exp (-logLoss R k N s) ≤ nativeRadius R k N s := by
  have hp : 0<nativeRadius R k N s := by
    refine mul_pos (prod_pos (fun j _=>?_)) (positive_seed R N s)
    exact Real.rpow_pos_of_pos (zero_lt_one.trans (R.alloy.B.a.fits.delayed (j+1))) _
  apply (Real.exp_le_exp.mpr _).trans (Real.exp_log hp).le
  exact neg_le.mp (le_max_right (0:ℝ) _)

private theorem fibre_first {I H : Type} [Fintype I] [Fintype H] [DecidableEq H] (h : H) :
    fibre (Prod.fst : H×I→H) h=({h} : Finset H)×ˢ(univ : Finset I) := by
  ext ⟨a,i⟩; simp [fibre,eq_comm]

theorem original_pattern {I : Type} [Fintype I] [DecidableEq I] (R : Run G)
    (simple : G.Simple) {k N per : ℕ} (T : Slices R.family.path.levels per) (hk : k<N)
    (F : I→ Config G (R.family.side N per)→ℝ) (a : I→Site (R.family.side N per)) (s : ℕ)
    (cont : ∀ i,Continuous (F i)) (sym : ∀ i,GaugeInvariant (F i))
    (unit : ∀ i U,|F i U| ≤ 1) (loc : ∀ i,LocalOn (halo s {a i}) (F i))
    (large : Fintype.card I ≤ (R.family.side k per).val)
    (v : ℕ→ℝ) {D η ε : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η) (hε : 0<ε) (small : ε ≤ 1/4)
    (top : v (traversal T hk.le).depth=0)
    (offset : ∀ j,0<j → j<(traversal T hk.le).depth → |v j| ≤ η)
    (L : ℕ) (posL : 0<L)
    (room : Fintype.card I*logLoss R k N (s+scale (traversal T hk.le)*Fintype.card I)+D ≤ L)
    (budget : let d:=traversal T hk.le
      let χ:=charge (Fintype.card I) (spacing (R.alloy.B.a.budget k).B L)
      (Fintype.card I : ℝ)*Real.exp (-2*D)+
        χ*(2*(d.depth:ℝ)*(scale d:ℝ)^4*4*(η*(R.alloy.B.a.clock.kernel.penalty*2))) ≤ ε^2) :
    let d:=traversal T hk.le
    let β:=RGComparison.Core16.line R.family.path per k N
    let W:=fun U=>∏ i,F i U
    |mean d (WilsonUniformUnmarkedInletSignedResponse.line β v 1) W 1-mean d β W 1| ≤ 3*ε := by
  intro d β W
  let A:=R.family.path
  let marked:=(R.again simple).1.scrim
  let m:=Fintype.card I
  let u:=s+scale d*m
  let P:=A.levels.budget N
  let M:=(A.levels.budget k).B
  let rad:=spacing M L
  let χ:=charge m rad
  have point: (A.rep N per k).p=A.levels.budget k := (R.T.choice.represents N per k hk.le).vac
  obtain ⟨x,uniq,near⟩:=distinct_fine d a large
  obtain ⟨J,dense,away⟩:=packed_copies (home d ∘ x) rad
  have nonvoid : J.Nonempty := by
    by_contra! empty
    rw [empty,card_empty,zero_mul] at dense
    exact (Nat.not_lt_of_ge dense) Fintype.card_pos
  let H:=↥J
  letI : Nonempty H := nonvoid.to_subtype
  let V:=H×I
  let g : V→H:=Prod.fst
  let b (h : H) := liftSite d h.val
  let root (i : V) := b i.1+x i.2
  let X (i : V) := halo u {root i}
  let o (j : ℕ) (i : V) := track T (root i) j
  let F' (i : V) (U : Config G (R.family.side N per)) := F i.2 (pull 1 (b i.1) U)
  have at_k (i : V) : o k i=i.1.val+home d (x i.2) := track_move T hk.le _ _
  have inj : Injective (o k) := by
    intro i j e
    rw [at_k,at_k] at e
    by_cases h : i.1=j.1
    · exact Prod.ext h (uniq (add_left_cancel ((congrArg (fun z:H=>z.val+home d (x i.2)) h).symm.trans e)))
    have hh:=away _ i.1.property _ j.1.property (fun eq=>h (Subtype.ext eq)) i.2 j.2
    simp only [comp_apply,e,separation_self] at hh
    omega
  have apart (i j : V) (h : g i≠g j) :
      2*(A.rep N per k).p.B+4*(2*(A.rep N per k).p.B+1)*L<separation (o k i) (o k j) := by
    rw [at_k,at_k,point]
    exact away _ i.1.property _ j.1.property (fun eq=>h (Subtype.ext eq)) i.2 j.2
  have next (j : ℕ) (_ : k ≤ j) (hj : j<N) :
      (A.levels.clock.op j per).ratio.parent ∘ o (j+1)=o j :=
    funext fun i=>track_step T (root i) hj
  have occupies (i : V) : o N i∈X i := by
    change track T (root i) N∈halo u {root i}
    rw [track_end]; exact halo_subset u _ (mem_singleton_self _)
  have cont' (i : V) : Continuous (F' i) := (cont i.2).comp (continuous_pull ..)
  have sym' (i : V) : GaugeInvariant (F' i) := translate_invariant (sym i.2) _
  have unit' (i : V) (U) : |F' i U| ≤ 1 := unit i.2 _
  have loc' (i : V) : LocalOn (X i) (F' i) := ball_local (loc i.2) (near i.2) _
  have bill (i : V) :
      Real.exp ((P.supportExponent+1)*coverNumber P.B (X i))*seedRadius R N u ≤ Bandage.far R.alloy.B.a N := by
    have lim : (coverNumber P.B (X i):ℝ) ≤ (2*(u:ℝ)+1)^4 := by exact_mod_cast ball_cover P (root i) u
    have le := mul_le_mul_of_nonneg_left lim (show 0 ≤ P.supportExponent+1 by linarith [P.exponent_pos])
    calc _ ≤ Real.exp ((P.supportExponent+1)*(2*(u:ℝ)+1)^4)*seedRadius R N u :=
               mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr le) (positive_seed R N u).le
         _ = _ := by unfold seedRadius; change Real.exp _*(_*Real.exp (-(P.supportExponent+1)*_))=_
                     rw [neg_mul,mul_left_comm,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  have tape := calibrated_corridor A _ _ _ R.doors R.T.choice marked.costs.night marked.back
    N per k hk (Stock.census V) (fun i U=>(F' i U:ℂ)) X o inj next occupies
    (fun i U Z eq=>congrArg Complex.ofReal (loc' i U Z eq))
    (fun i h U=>congrArg Complex.ofReal (sym' i h U))
    (fun i=>(Complex.continuous_ofReal.comp (cont' i)).measurable)
    (fun i U=>by simpa using unit' i U) (fun _=>seedRadius R N u) (fun _=>positive_seed R N u) bill
  have wCont : Continuous W := continuous_finsetProd _ fun i _=>cont i
  have wSym : GaugeInvariant W := fun t U=>prod_congr rfl fun i _=>sym i t U
  have wUnit (U) : |W U| ≤ 1 := by
    change |∏ i,F i U| ≤ 1; rw [abs_prod]
    exact prod_le_one (fun _ _=>abs_nonneg _) (fun i _=>unit i U)
  have copies (h : H) (U) : word g F' h U=W (pull 1 (b h) U) := by
    rw [word,fibre_first,Finset.prod_product]; simp [F',W]
  have fibres (h : H) : (fibre g h).card ≤ m := by rw [fibre_first,card_product]; simp [m]
  have purchase : 1 ≤ (A.levels.budget k).supportExponent := by linarith [(marked.costs.night.endow k).2.1]
  have hsize : ((A.S.side N per).val:ℝ)=((A.S.side k per).val:ℝ)*(scale d:ℝ) := by
    exact_mod_cast (side_scale d).symm
  have density : ((A.S.side k per).val:ℝ)^4 ≤ (Fintype.card H:ℝ)*(χ:ℝ) := by
    have dn : (A.S.side k per).val^4 ≤ Fintype.card H*χ := by
      rw [show Fintype.card H=J.card from Fintype.card_coe J]
      rw [site_card] at dense; exact dense
    exact_mod_cast dn
  have coef : 0 ≤ 2*(d.depth:ℝ)*(scale d:ℝ)^4*4*(η*(R.alloy.B.a.clock.kernel.penalty*2)) := by
    have ht := R.alloy.B.a.clock.kernel.penalty_pos; positivity
  have affordable : (Fintype.card V:ℝ)*Real.exp (-2*D)+
      2*(((d.depth*((A.S.side N per).val^4*4)):ℕ):ℝ)*(η*(A.levels.clock.kernel.penalty*2))
        ≤ (Fintype.card H:ℝ)*ε^2 := by
    let K:=2*(d.depth:ℝ)*(scale d:ℝ)^4*4*(η*(R.alloy.B.a.clock.kernel.penalty*2))
    calc _ = (Fintype.card H:ℝ)*((m:ℝ)*Real.exp (-2*D))+((A.S.side k per).val:ℝ)^4*K := by
              rw [show Fintype.card V=Fintype.card H*m from Fintype.card_prod ..]
              push_cast; rw [hsize]
              change _+2*(_*(_*4))*(η*(R.alloy.B.a.clock.kernel.penalty*2))=_
              dsimp only [K]; ring
         _ ≤ (Fintype.card H:ℝ)*((m:ℝ)*Real.exp (-2*D))+(Fintype.card H:ℝ)*(χ:ℝ)*K :=
              add_le_add_right (mul_le_mul_of_nonneg_right density coef) _
         _ ≤ (Fintype.card H:ℝ)*ε^2 := by
              rw [mul_assoc,←mul_add]; exact mul_le_mul_of_nonneg_left budget (Nat.cast_nonneg _)
  exact separated_endpoint A R.T.choice T hk.le g F' cont' sym' unit' W wCont wSym wUnit
    Subtype.val copies (o k) inj m L fibres apart posL (le_max_left ..) hD (pays_radius R k N u)
    purchase room tape v top hη offset hε small affordable

end YM.Integration.InletSusceptibility.Packet
