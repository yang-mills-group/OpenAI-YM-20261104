import YM.MergeProof.North.Burrough
import YM.Contact.Invoice
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d w:ℕ)(h:ℤ){x:ℝ} {j : ℕ→ℕ}
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "J"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
variable (hG:G.Simple)(t:ℝ) (hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hj:Tendsto j atTop atTop)
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hV:Velour C (renal C.path.levels) r D')
variable {b a:ℝ}(hb:0<b)(ha:0<a)(hp:(D:ℤ)+h=d+w)
local notation "F"=> fun i=> fuga C.path.levels (i+1)
local notation "A"=> fun (i:ℕ)=> twoStakes C (j i) i d w h b a
local notation "Z'"=> fun (i:ℕ)=> holder C.path.levels (j i) i δ η (δ (i+1)) ((A) i)
local notation "Ne"=>Note C.S
local notation "M"=> (((d:ℝ)+w+8)*(1-t))
open Accent Source Extra.Histories
variable {u ψ:ℕ→ℝ}{W:Worth}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
local notation "X"=>bling C.path.levels
variable (hL:Tally C.path.levels)
include hL
local notation "c"=>pitts C
local notation "e"=> fun i=> 4*(1+(C.path.levels.params i).columns)*(2*(C.S.a (i+1)^D*(X i*(4*(1/((Z') i))))))
include hj hT hV hG hW hb ha hp
lemma priced (k:ℕ)(hK:C.ref D ≤ k)(he: -(1/32)< M) : ∀ᶠ i in atTop, (0<(Z') i ∧ march (fun _:Unit=>(c) i) η k i () ≤ δ i * (((Z') i)/(16*X i)))∧ 32*(1+(C.path.levels.params i).columns)* (c) i * ‖alto C.path k D‖*((e) i/gainChart C.path i k) ≤ fly C.path.levels D k/2:=by
   let S:= C.S; have ht:Ne (c) (1/32):= Note.bell_exp S _; have hx:= sea_charge C D d w h hG t hT hj hV hb ha hp hL; have hy:= Note.note_a S; have hf:= banket C hG
   let q:= fly C.path.levels D k; have hq:0<q:= hW.grows _ _ hK
   have hr:= (Note.notes S 16 (by norm_num)).mills hf; have hI:= (mintN C hG).1.mills (hx.splits hr)
   let v i:= 1+(C.path.levels.params i).columns
   let w:= ‖alto C.path k D‖; have hw:0 < w:=by unfold w; rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
   have hz: Ne v 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have hc:= ((Note.notes C.S 32 (by norm_num)).mills hz).mills ht|>.mills (Note.notes _ w hw)
   have haD:= (Note.note_a S).scales C.path.levels.fits.mesh |>.powerN D
   have hE: Ne e (-M):= by
       have h₀:=Note.notes S 4 (by norm_num); exact (((h₀.mills hz).mills ((Note.notes S 2 two_pos).mills (haD.mills (hf.mills (h₀.mills ((Note.notes S 1 one_pos).splits hx)))))).swapP (by ring))
   have hF:Ne (fun i=>gainChart C.path i k) (1/8):=by
       let r:ℝ:=Real.exp ((1/8:ℝ)*Q k)
       have hv:= (Note.bell_exp S (1/8)).splits (Note.notes S r (Real.exp_pos _))
       unfold gainChart; simp_rw [mul_sub,Real.exp_sub]; exact hv.swapP (sub_zero _)
   have hH:= (hc.mills (hE.splits hF)).outweigh (Note.notes C.S (q/2) (half_pos hq)) (by linarith)
   let u i:= ((c) i)* (S.a i/S.a k)^(D+1)*(1/q)
   have hJ:= (ht.mills ((hy.splits (Note.notes S _ (S.a_pos k))).powerN (D+1))).mills (Note.notes S (1/q) (by positivity)); have hh:=hJ.outweigh hI (by push_cast; linarith)
   filter_upwards [eventually_ge_atTop k,hH,hh] with i hi hk hh
   have hU := seeing C D hW (ht.pos i) i k hK hi
   refine ⟨⟨hx.pos _,hU.trans (le_trans ?_ hh)⟩,hk⟩
   apply mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (fly_le C i D) hq.le) (mul_nonneg ((ht.pos i).le) (pow_nonneg (div_nonneg (S.a_pos i|>.le) (S.a_pos k|>.le)) _))
omit hL hj hT hW hb ha hp
lemma lampDown (p:ℕ):∀ᶠ i in atTop, 32*(ranula (P) i) ≤ C.S.a p ∧ C.S.a (i+1)*((((J (i+1)).B^2+1+2*blast C.path.levels i):ℕ):ℝ)≤ C.S.a p:=by
   have hz:C.S.Gentle:=C.path.levels.fits.mesh
   have hQ:= briar C hG hV
   have hZ: Ne (fun i=> (C.S.block i).val) 0:= ⟨fun i=>Nat.cast_pos.mpr (C.S.block i).pos,C.path.levels.fits.mesh⟩ -- change gentle
   have hY:= ((hQ.scales hz|>.powerN 2).swapP (by norm_num : (↑(2:ℕ):ℝ)*0=0)).extra ((hZ.mills (hQ.powerN _)).swapP (by norm_num : (0:ℝ)+ ↑(2:ℕ)*0=0))
   have hR:Ne (ranula C.path.levels) (-1):=by
       change Note C.S (fun i => 128*(↑(quotaStem C.path.levels i):ℝ)*C.S.a (i+1)) (-1)
       simpa only [ranula,quotaStem,Nat.cast_add,Nat.cast_pow,Nat.cast_mul,mul_zero,zero_add] using! (((Note.notes C.S 128 (by norm_num)).mills hY).mills ((Note.note_a C.S).scales hz))
   have hh:= (Note.notes C.S (C.S.a p) (C.S.a_pos p)); refine ((Note.notes C.S 32 (by norm_num)|>.mills hR).outweigh hh (by norm_num)).and ?_
   have hv: Ne (fun i=> ((((J (i+1)).B)^2+1+2*blast C.path.levels i:ℕ):ℝ)) 0:=by
       unfold blast quotaStem; push_cast; have he:Ne (fun i=> (((J (i+1)).B:ℝ))^2) 0:= ((briar C hG hV).scales hz|>.powerN 2).swapP (by norm_num); exact (he.extra (Note.notes _ _ (by norm_num))).extra (((Note.notes C.S 2 two_pos).mills ((Note.notes C.S 1024 (by norm_num)).mills hY)).swapP (by norm_num))
   exact ((Note.note_a C.S|>.scales hz).mills hv).outweigh hh (by norm_num)
end YM.MergeProof.Ribbons
