import YM.FVAAlt2.Turn.Unit
import YM.FVAAlt2.Turn.Revenue
/-! exact fixed-of-unit high. `o` assumption (birth is scalar) attested
 by S.W.supplier later.See also pose_propagation which doesn't depend on unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Town
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve High Detect Domain Tone Tone.Frame Momentum Outlook Motif Literal Halo Mach Mach.Pole
open _root_.YM.MS.Wind _root_.YM.MS.City Native Native.Wilsonian Native.Studio Lattice
open Motions Leading Knobs Menus Program Local.Physical Land Cylinder Lifting
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge} {m n k:ℕ} {r x:ℝ}{z:ℂ} {B:Deck G}
local notation "Φ"=> baseM G
local notation "pC"=> piece (A:=LightMode G Cover) (1:ℂ)
-- every spectral caller OK for these basis. rank-zero seeds unchanged. PS coupling & scale.V.
def gold (G:Gauge) (n:ℕ): Dot G Cover := if n=0 then piece 1 else 0
lemma gold_l (n:ℕ): levels (A:=Branch G Axis) 0 pC n= gold G n:= by
 by_cases h:n=0; rw [h,levels, Nat.cast_zero,zero_add,gold,if_pos rfl]; apply Subtype.ext; exact rank_hat _ |>.mp (Rails.coin _)
 rw [ gold, if_neg h]; apply Subtype.ext; funext t; by_cases hm:(t.length:ℤ)=(n:ℤ)+0; · change mask _ _ _=_; rw [Book.enough t hm]; cases t; simp at hm; omega; rfl
 exact strange t hm
lemma bank_sub (V:Cn) : substitute V (gold G)= gold G:=by funext i; rw [ rules ]; simp_rw [gold]; by_cases h:i=0 <;> simp [Program.cut,h,apply_ite]
lemma gold_flat (T:Team)(z:ℝ) : wobble G T z (gold G)= gold G:= by
 unfold wobble; rw [LinearMap.comp_apply, bank_sub]; funext n; rw [rolls]; unfold gold; rw [Finset.sum_eq_single (n,0),if_pos rfl]
 · apply Subtype.ext; ext l; split <;> rename_i h <;> rw [train_v,offer] <;> (cases l<;> simp [*,piece,coin])
 · intro a ha hh; rw [ if_neg ( by exact fun he=> hh (Prod.ext (by have h:= mem_antidiagonal.mp ha; omega) he)) ]; simp
 simp
-- template high.Act
variable (i:Plaid B 0)
def rentFree (B:Deck G)(i:Plaid B 0) : Acts B 0:= fun n=> if n=0 then { register:= fun j=> if j=Land.read i then 1 else 0, proof:=0 } else 0
lemma placid : FitOrder (Land.read i) (rentFree B i 0):= ⟨fun _ _ _=>rfl,fun _ _=>rfl⟩ -- Classical not defeq
abbrev flame (G:Gauge): Actor G:= fun _=> gold G
lemma no_boil (n:ℕ)(J: Glyph B 0)(x:ℝ): oil (rentFree B i) J n x=if n=0 ∧ J=Land.read i then 1 else 0:= by by_cases h:n=0 <;> by_cases H:J=Land.read i <;> simp [oil,rentFree,h,H] <;> exact Polynomial.eval_zero -- maybe
lemma score_fixed {M:RichBook B}(T:Team)(k:ℂ)(h:M.menu 0 _ i.2= k • gold G) : scorePl M T (rentFree B i) = k • flame G:= by
 have hz i' : (prim (rentFree B i) i')=0:= by funext t; unfold prim rentFree; split_ifs <;> rfl
 funext x n; unfold scorePl; rw [Pi.add_apply,motto,hz,map_zero,map_zero, add_zero,Pi.zero_apply,add_zero ]; unfold Menus.rentPl; simp_rw [no_boil]; rw [Finset.sum_eq_single ( Land.read i ),Finset.sum_eq_single (0,n),if_pos ⟨ rfl,rfl⟩,one_smul]; · unfold Glyph.preamblePl; change wobble G T x (M.menu 0 _ i.2) n=_; rw [h,map_smul,gold_flat]; rfl
 · rintro ⟨a,b⟩ ha hh; rw [ if_neg (fun h=>hh (Prod.ext h.1 (by have ht:= mem_antidiagonal.mp ha; omega))),zero_smul]
 · simp
 · intro j hj hh; exact sum_eq_zero fun u _=> by rw [ if_neg (fun h=> hh h.2),zero_smul ]
 simp
omit i
-- Weak Sat proof, `skyline G p` supplied; no relying on coincidental choice.
def safeP (G:Gauge)(n:ℕ)(x t:ℝ): Law G:= Archive 0 (winter G) n (x,t)
private abbrev logF (G:Gauge) (n:ℕ): Wind.Flow G:= fun _=> if n=0 then coin 1 else 0
private lemma releases(G:Gauge) (t:ℝ) : safeP G n t=logF G n:= by funext k; exact archive_unit ..
private lemma asmooth(n:ℕ): TouchF (logF G n):= by intro E _ _ f w he h; by_cases hm:n=0 <;> (cases w <;> unfold logF <;> first | (simp_rw [if_pos hm]; exact contDiff_const) | (simp_rw [if_neg hm]; exact contDiff_const)) -- fix
private lemma costFree (G:Gauge): (Wiref G (logF G n))=0:=by
 funext v l; change Heat.orbit _ μzone (logF G n v) l=0; rw [finite_cc μzone (period0 _ cour0 (main_f G) (asmooth n))]; unfold Ccy logF; simp_rw [at_trc]; by_cases h:n=0 <;> simp [coin,h]
private lemma emits (G:Gauge) (V: Dec G) (n:ℕ) (x:ℝ) (t:ℝ) : Wind.path 1 n 0 V (safeP G) x t=0:= by
 unfold Wind.path; rw [one_smul,Finset.sum_apply, Finset.sum_apply]; apply Finset.sum_eq_zero; intro i hi; rw [releases]; change tree Landau.parity _ _ ((logF G i) t) = 0; by_cases h:i=0; · unfold logF; rw [if_pos h]; exact coinless ..
 change (treeP G _ (fun t=>if i=0 then coin 1 else 0)) t=_; simp_rw [if_neg h]; exact congr_fun (map_zero (treeP G _)) t
lemma self_pin (V: Dec G) : Lobby (flame G) V (safeP G):=by
 constructor
 · simp_rw [releases]; exact fun n _=> asmooth n
 · intro n t; refine ⟨0,fun u l hl=>?_⟩; cases l; simp at hl; rw [safeP, archive_unit]; split_ifs <;> rfl
 intro n x; rw [releases]; unfold Sat; rw [costFree]; refine ⟨?_, fun t=>?_⟩; · unfold logF flame gold; split_ifs; exact Eq.symm ( Cylinder.coin_turn .. ); exact (map_zero Tone.run).symm
 rw [ emits,Pi.zero_apply,zero_add ]; exact fun i=> hasDerivAt_const ..
def Genesis (U:RichBook B): Prop:= ∀ (j:Plaid B 0) (c:ℝ),( Land.read j).read=(c:ℂ) • coin 1 → U.menu 0 _ j.2=(c:ℂ) • gold G
lemma markTOP {U: RichBook B}{A: Land.Booked B}(V: MS_Data G A)(h:Genesis U)(T:Team)(i: Plaid B 0): Fixed ( col ( horizonPl U T ( rentFree B i ) ) ) (Archive 0 ( V.marks 0 i )) false 0 0 := by
 obtain ⟨c,hc,H⟩:= winter_show G A V i; obtain hh:= h i c hc
 have he : horizonPl U T (rentFree B i)=(c:ℂ) • safeP G:= Lobby.unique ((score_fixed i T (c:ℂ) hh) ▸ foyer (aquaPl U T (rentFree B i))) ((self_pin (skyline G T)).static (c:ℂ)) -- notation
 have hw : col (horizonPl U T (rentFree B i))=Archive 0 (V.marks 0 i):= by -- log evaluation of safeP uses log evaluated at exp t; constant! important.
    rw [he,H]; funext n x; rcases x with ⟨s,t⟩; simp only [col,Pi.smul_apply,safeP,archive_unit]; -- match
 rw [hw]; obtain hu : Good false G 0 (Archive 0 (V.marks 0 i)):= (fieldD V.bulkOK (V.markOK 0 i) wisdom ((A.law 0 i).moodQ)).good; intro j hj r hr E _ _ w hw h; exact Like.same (S:=High.meet.primary) (fun i=> (Plane.at_start p_gain.le i).1.le) (hu E j w hw (h.symm ▸ hr)) -- check namespace

end YM.MS.FVA.Town

