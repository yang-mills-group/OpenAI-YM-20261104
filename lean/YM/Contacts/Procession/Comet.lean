import YM.Contacts.Procession.Bonus
/-!
# Post & pre costs on this same path

Keep polynomial cost in e.Z. Used on any join horizon (pre-calibration of frames).
-/
noncomputable section
namespace YM.Contacts.Procession.Port
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales
set_option autoImplicit false
variable {G:Gauge}{n k i r l p:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
open Trace Pigment Local
variable (T:MapPrices)(G) (j v:ℕ)
-- n: field Horizon, k: rank, r: derivative budget of root (>=rd−?), v target power age moment. j stage
abbrev luxury (p:ℝ)(L:Side)(n:ℕ) := Real.exp (-(Real.log (L.val:ℝ))/2) / (p*(L.val:ℝ)^n)
def Toast (T:MapPrices)(j n k r:ℕ) (p:ℝ) (L:Side):Prop:=
    let d:=n+1-k
    Odd L.val → ∀ (R: Spine.voyage L) (s t:ℝ≥0), (t:ℝ)*2≤T.α j → (2*(t:ℝ)/(L.val:ℝ))*(k+1) ≤ s →
    (∀ (w:List Axis),w.length ≤ d → Row.strip (advanceC L R w) (T.α j) (purse T j/(L.val:ℝ)^(1+w.length)))→
    ∀ (F:Pigment.Ribbon (Dye G) k), IsLinearMap ℝ F → Clear F d → ∀ b≥(0:ℝ),∀ x y:Dye G,∀ z:Cover, rent L z=0 → ∀ w:E4, ‖w‖+ (L.val:ℝ)⁻¹*4 ≤ 4 → Pigment.Weight F r (bath s v _) x b→ Pigment.Weight (Local.Bery (Origin.bleed G R) z w F) r (bath t v _) y (luxury p L n*b)
lemma arranged (k n r:ℕ)(p:ℝ)(hp:0<p)(h:n+1-k ≤ r)(he:n+1-k ≤ v) : ∃ P:ℕ,∀ L:Side, P≤L.val→ Toast G v T j n k r p L := by
    let d:=n+1-k; let s:=rentCheque T j; let Q:=purse T j; obtain ⟨c,hc,H⟩:= coatContract s v (rent_pos T j) (Dye G) (Dye G) Q (purse_pos T j).le; obtain ⟨B,hB,hb⟩:= Pigment.Local.bargain (X:=Dye G) (Y:=Dye G) r v k d c s hc he h; obtain ⟨K,hK⟩:= pessimistic (b:=0) le_rfl (1:ℝ) (B*p) zero_lt_one;
    refine ⟨K,fun L hL=>?_ ⟩; intro hL₀ R σ η hs ht hr F hF he b b0 x y z hy w hw hb'; let U:= R; let l:ℝ:=L.val; have hl:1≤l:= by unfold l; exact_mod_cast (show 1≤L.val from L.property)
    have hh : Weight (Bery (Origin.bleed G U) z w F) r (bath η v _) y (B*l⁻¹^(k+d)*b):= by
       apply hb L (Origin.bleed G R) σ η F z x y w hy hL₀ hF he _ _ ht hw b b0 hb'; · intro v hv x; unfold Pulse.Spine.Quill.Balanced; simp_rw [mul_comm (Pulse.Spine.hook _ _ _ x _) _]; exact ((H L η hs _ _ (show Row.strip (advanceC L (Origin.bleed G R) v) s (purse T j/l^(1+v.length)) from (by rw [Origin.advance_bleed]; exact Origin.bleed_strip (G:=G) (s:=s) (hr v hv) (div_nonneg (purse_pos T j).le (by positivity))))).rows x)
       apply NNReal.coe_le_coe.mp; change _≤ T.α _; linarith only [hs, NNReal.coe_nonneg η]
    intro f a ha hb''; apply (hh f a ha hb'').ist; apply mul_le_mul_of_nonneg_right _ ha; apply mul_le_mul_of_nonneg_right _ b0; unfold luxury; rw [inv_pow,← div_eq_mul_inv]; calc
       _ ≤ B/l^(n+1):= div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_right₀ hl (by unfold d; omega))
       _≤ _:=(le_div_iff₀ (mul_pos hp (by change 0 < l^n; positivity))).mpr (le_trans (le_of_eq ?_) (hK L hL).2)
    field_simp; ring
-- extend coupon list through next smoothing stage entrance.
def pleat (j n k r v:ℕ) (p:ℝ):ℕ:= if h: 0<p ∧ n+1-k≤ r∧ n+1-k≤ v then (arranged (G:=G) T j v k n r p h.1 h.2.1 h.2.2).choose else 0 -- order infer
-- multiplier choose from pre-block data only
def charge (j:ℕ)(p:ℝ):ℕ:= Finset.sup (Iic j) (fun n=> Finset.sup (Iic j) (fun k=> Finset.sup (Iic j) (fun r=> Finset.sup (Iic j) (fun v=> pleat G T j n k r v p))))
lemma salutes (T:MapPrices)(p:ℝ)(hp:0<p)(h:n+1-k≤r)(he:n+1-k ≤ v)(hk: k≤j)(hn:n≤j)(hr:r≤j)(hv:v≤j) (L:Side)(hy: charge G T j p ≤ L.val) : Toast G v T j n k r p L:= by
    refine (arranged (G:=G) T j v k n r p hp h he).choose_spec L ((le_trans (b:=charge G T j p) ?_ hy)); exact Finset.le_sup_of_le (Finset.mem_Iic.mpr hn) (Finset.le_sup_of_le (Finset.mem_Iic.mpr hk) (Finset.le_sup_of_le (Finset.mem_Iic.mpr hr) (Finset.le_sup_of_le (Finset.mem_Iic.mpr hv) ((show pleat G T j n k r v p=_ from dif_pos ⟨hp,h,he⟩).symm.le))))
structure Rival where
  ups: MapPrices→ℕ→ℝ
  hold T j:0<ups T j
variable {G}
def Decked (Z:Rival)(e:Oasis G):Prop:= ∀ i,let j:=e.J (i+1); charge G e.T j (Z.ups e.T j)≤(e.L i).val
open Org PhysicalNext.Repeat.Legato
def addBid (p:BidTri G)(P:Rival): BidTri G:= ⟨fun T i=> max (p.w T i) (charge G T i (P.ups T i)),p.pay⟩
lemma decked {p:Passage G}(t:BidTri G)(P:Rival)(h: admits (addBid t P) p): admits t p ∧ (∀ i,let j:=p.A.B.a.clock.J (i+1); charge G p.M.K j (P.ups p.M.K j) ≤ (mainFlag p.A.B.a i).L.val) := ⟨fun i=>⟨(le_max_left ..).trans (h i).1,(h i).2⟩,fun i=> (le_max_right ..).trans (h i).1⟩
abbrev upright (e:Oasis G) (R:Rival) (n i) := luxury (R.ups e.T (e.J (i+1))) (e.L i) n
lemma cheers (Z:Rival){e:Oasis G}(hz:Decked Z e)(h:n+1-k≤ r)(hi:n+1-k ≤ v) : ∀ᶠ i in atTop,∀ N:ℕ,i<N→let W:= Origin.bleed G (e.vintage i N); ∀ F:Pigment.Ribbon (Dye G) k, IsLinearMap ℝ F → Clear F (n+1-k) → ∀ b≥(0:ℝ),∀ x y:Dye G,∀ z:Cover,rent (e.L i) z=0 → ∀ w:E4, ‖w‖+(↑(e.L i).val:ℝ)⁻¹*4≤4 → Weight F r (e.Bx v (i+1)) x b → Weight (Bery W z w F) r (e.Bx v i) y (upright e Z n i*b):= by
    filter_upwards [e.a.fits.deep.eventually_ge_atTop (r+v+n+k+3), e.deep_lean (2*((k:ℝ)+1))] with i hi' hP N hN; let j:= e.J (i+1); have he:e.J i≤j:= e.a.fits.mono (Nat.le_succ i); change r+v+n+k+3≤ e.J i at hi'; have hk (l:List Axis)(ht:l.length≤ n+1-k) : Row.strip (advanceC (e.L i) (e.vintage i N) l) (e.T.α j) (purse e.T j/(e.L i).val^(1+l.length:ℕ)):= by
        apply strip_mono ((e.lamp.costs N i hN).2.2.2 l (ht.trans (by change _≤ e.J (i+1)-2; change _≤ j-2; omega))).1 le_rfl; gcongr; exact le_max_right ..
    have ht:e.ξ i ≤ e.flag i:= le_trans (le_mul_of_one_le_left (by positivity) one_le_two) ((e.halos i).trans (div_le_self (by positivity) (by norm_num)))
    intro W; refine salutes G j v _ (Z.ups e.T j) (Z.hold ..) h hi (by omega) (by omega) (by omega) (by omega) _ (hz i) (e.a.S.block_odd i) (e.vintage i N) (e.ξ (i+1)) (e.ξ i) ?_ ?_ hk; · rw [mul_comm]; exact (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) zero_le_two).trans ((by exact_mod_cast e.silk i : 2*(↑(e.flag i):ℝ) ≤ e.κ (i+1)))
    refine le_trans (le_of_eq ?_) hP; field_simp
end YM.Contacts.Procession.Port
