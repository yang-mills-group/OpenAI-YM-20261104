import YM.OPE.Coverage.Tour
import YM.Push.PRICE_COMPILER.Post

/-!
## Rehearsal clocks before the actual bar and waits
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Function Filter Set Lattice Wilson RG Next.Rank Bid Push.PriceCompiler Precision Supply Real
open scoped Topology
variable {G : Gauge} {X:RG.Supply.Sheet G} {w:Rolls X} {D:Protection w} (T:Delays D)

lemma earlier_parole {T T':Delays D}(h:DelayLe T T') (b:Bar T'): ∃ c:Bar T,c.value=b.value:=by
   exact ⟨{b with ready:=(h.beta _).trans b.ready},rfl⟩

def blank (Z:Bar T):Wait Z:=⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
variable (v:ℝ→ℕ→ℝ)
def reset: Delays D:={T with scaleEntry:=fun j x=> max (T.scaleEntry j x) (max (v x j) (Real.exp (Real.exp ((w.L j).val))))}
-- Crude delay, does not affect minLength
lemma reset_up : DelayLe T (reset T v):=⟨le_rfl,fun _ _=>le_max_left ..,le_rfl,le_rfl⟩

variable (p : ℝ → Option (Σb:Bar T, Wait b))
def allowance (j:ℕ)(s:ℝ) := ((p s).elim 0 fun ⟨b,w⟩=> w.readyHere j)
lemma allowed {s b a} (h:p s=some (Sigma.mk b a))(j:ℕ): (a:Wait b).readyHere j=allowance T p j s:=by simp [allowance,h]

def round (s:ℝ):ℕ:= Nat.ceil (Real.sqrt s)
lemma rounds :Tendsto (fun s=>(round s:ℝ)/s) atTop (𝓝 0):=by
    have h: ∀ᶠ i:ℝ in atTop,(round i:ℝ) ≤ Real.sqrt i +1:=Eventually.of_forall fun i=>(Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
    have ht:Tendsto (fun i:ℝ=> Real.sqrt i / i) atTop (𝓝 0):=by
       refine (tendsto_const_nhds (x:=(1:ℝ)) |>.div_atTop Real.tendsto_sqrt_atTop).congr' ?_
       filter_upwards [eventually_gt_atTop (0:ℝ)] with i hi
       conv_rhs => rhs; rw [← Real.sq_sqrt hi.le]
       field_simp [ne_of_gt (Real.sqrt_pos.mpr hi)]
    have hv:Tendsto (fun i:ℝ=> Real.sqrt i / i+1/i) atTop (𝓝 0):=by
       have hv' := (ht.add (Tendsto.div_atTop (tendsto_const_nhds (x:=(1:ℝ))) (show Tendsto id (atTop : Filter ℝ) _ from tendsto_id))); exact add_zero (0:ℝ) ▸ hv' 
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv ?_ ?_
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with i hi; exact div_nonneg (Nat.cast_nonneg _) hi.le
    filter_upwards [eventually_gt_atTop (0:ℝ),h] with i hs hi
    rw [← add_div]; apply div_le_div_of_nonneg_right ?_ hs.le
    exact hi
variable {T T' : Delays D} {Z:Bar T}

def supplement {Z':Bar T'} (I:Wait Z)(Y:Wait Z'):Wait Z':=
    {Y with readyHere j := max (I.readyHere j) (Y.readyHere j)
            minLength := max I.minLength Y.minLength
            window j s := I.window j s+Y.window j s+round s
            sublin j:=by simpa only [Nat.cast_add,add_div,zero_add] using (((I.sublin j).add (Y.sublin j)).add rounds)}
-- parenthesization should be ht.add hV then rounds (not hT.add (hV).add ambiguous syntax)
theorem pay_across {Z':Bar T'} {A:Levels G}{I:Wait Z}{Y:Wait Z'}(h:DelayLe T T')(hz:Z.value=Z'.value)(hs:I.minLength ≤ Y.minLength)(ht:I.readyHere ≤ Y.readyHere)(he:I.window ≤ Y.window) (hv:Paid Y A):Paid I A where
   kernel := hv.kernel
   bar := hv.bar.trans hz.symm
   stage := hv.stage
   firstZero := hv.firstZero
   firstOne := hv.firstOne
   lengths := hv.lengths
   theta := hv.theta
   pays i := (h.beta _).trans (hv.pays i)
   paysHigher i := by rw [hz]; exact fun hi=>(h.scale _ _).trans (hv.paysHigher i hi)
   periods i := hs.trans (hv.periods i)
   volume i p  := by
      exact (Nat.mul_le_mul (h.shells _) (Nat.pow_le_pow_right (show 0 < (_:ℕ) from by omega) (h.growth _))).trans (hv.volume i p)
   run j hj:= by
     obtain ⟨k,hk,hK,hv⟩:= hv.run j hj
     have hW:=he j (A.S.scale k)
     exact ⟨k,(ht j).trans hk,hW.trans hK,fun i hi hi' => hv i ((Nat.sub_le_sub_left hW _).trans hi) (hi'.trans (Nat.add_le_add_left hW _))⟩


end YM.OPE.Coverage
