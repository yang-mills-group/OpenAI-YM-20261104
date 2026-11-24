import YM.SchemeConversionRG11.FirstW.Fold.Fugue
/-! Pack with engineering conversion and Fleck budget on the insertion. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Lattice Pert Align Position Maxwell RawLabels MvPolynomial Warp SchemeConversionRG11 Horizon
open scoped BigOperators Classical Topology
variable {G:Gauge}{F:Labels.Frames G}{h:ℝ}
def twistC (v:ℝ)(z:Pack F): Pack F:= ⟨(↑(v^(-6:ℤ)):ℂ) • (Scale.gear F 6 v ∘ₗ z.val), by
 have H(p:E F 6) : ((↑(v^(-6:ℤ)):ℂ) • (Scale.gear F 6 v ∘ₗ z.val)) p= (↑(v^(-6:ℤ)):ℂ) • Scale.gear F 6 v (z.val p) := rfl
 refine ⟨fun p=>?_,fun p hp=>?_,fun p=>?_,fun s p=>?_⟩
 · rw [H]; apply Submodule.smul_mem; refine vaulted.mpr ⟨well_H _ _, ?_,send_H _ _⟩
   rw [Full.sections,LinearMap.comp_apply,Scale.gear_lifts]; exact change_weight (Full.sections 6 F (z.val p)) (show _∈ census G 2 from (vaulted.mp (show _∈Reel G from (suitsP z).sees p)).2.1) _
 · rw [H,(suitsP z).sunk _ hp,map_zero,smul_zero]
 · rw [H,H,map_smulₛₗ, show ∀ p:E F 6,bar F 6 (Scale.gear F 6 v p)= _ from fun p=> Scale.gear_conj F p v, (suitsP z).proofP p]; simp
 rw [H,H,map_smul,(suitsP z).torque s]; exact congrArg _ (Scale.gear_spin F (z.val p) s.ortho v).symm
 ⟩
lemma twisted (h : ℝ)(p:E F 6)(x:Dot G 6) : look x (cloak F (Scale.gear F 6 h p)) = look (lit 6 (Scale.resizer h G) x) (cloak F p) := by
 let B:=barks 6 x
 have H:salute 6 B=x:= bark_in x
 rw [←H, lit_any,seen,seen,Full.sections,LinearMap.comp_apply,Scale.gear_lifts]; exact Labels.eval_changed ..
lemma heightT (h : ℝ) (x:Dot G 6)(a:Who G 6): lit 6 (Scale.resizer h G) x a=h ^ fee a*x a := by
 let B:= barks 6 x; have H:salute 6 B=x:=bark_in x
 rw [←H,lit_any]; simp only [salute,Scale.resizer,LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply,map_smul,LinearMap.smul_apply,LinearMap.id_apply];rfl
lemma copaid (v:ℝ)(z: Pack F)(p:E F 6)(a b:Who G 6): loot (cloak F ((twistC v z).val p)) a b= ((v^(-6:ℤ)* (v ^ fee a)* v ^ fee b:ℝ):ℂ)* loot (cloak F (z.val p)) a b:= by
 change loot (cloak F ((↑(v^(-6:ℤ)):ℂ) • _)) _ _ = _
 have hh{x:ℂ}(p:Part G 6) : loot (x • p) a b=x*loot p a b := by simp only [loot,D1,Derivation.map_smul, MvPolynomial.coeff_smul, smul_eq_mul] -- type
 have he := second_turn _ _ (lit 6 (Scale.resizer v G)) (fun x=>twisted v (z.val p) x) a b
 let L:=lit 6 (Scale.resizer v G); have hv (x y:Who G 6): accord L x y=if x=y then v^fee x else 0 := by unfold accord L; rw [heightT]; split_ifs with h <;> simp_all
 rw [←robes_eq,map_smul,hh,robes_eq]; change (↑_:ℂ)* loot (cloak F (Scale.gear F 6 v (z.val p))) _ _=_; rw [he]; unfold L at hv; simp_rw [hv]
 rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]; rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)]; simp;ring
 · intro i _ hi; simp [hi]
 intro i _ hi; simp [hi]
-- matrix on E. Fleck ζ. function includes sign `−` for normalize later.
def carryR (n:Side)(t:ℝ)(z:Pack F) := Outfit (twistC t z)+ sleeve F n t
lemma unit_leg : cloak F ((freeTable F).unit 6) = 1:=by apply rename_injective Subtype.val Subtype.val_injective; change uncap _=uncap (1 : Part G 6); rw [stretch, Full.sections, LinearMap.comp_apply,physical_unit]; simp [uncap,Labels.unit]
section tests
variable {T:Itinerary}
lemma dear_chips (p:E F 6)(Z:ℕ→Pack F)(hp:Level (fun i=>T.gap i • Z i))(a b:Who G 6): Dear T (fun i=>loot (cloak F ((twistC (T.gap i) (Z i)).val p)) a b):=by
 have he:=BondW_fe p _ hp a b
 have ht (q:Pack F)(v:ℝ): loot (cloak F ((v • q : Pack F).val p)) a b=v • loot (cloak F (q.val p)) a b := by
   have ht: (v • q : Pack F).val p=(v:ℂ) • q.val p:=by rw [SetLike.val_smul,LinearMap.smul_apply]; exact RCLike.real_smul_eq_coe_smul (K:=ℂ) v _
   simp only [loot,ht,D1,←robes_eq,map_smul,Derivation.map_smul,coeff_smul, Complex.real_smul];rfl
 simp_rw [ht] at he; have hh:= ((T.cutoff.pow (fee a) |>.mul (T.cutoff.pow (fee b))).smul he); rw [smul_zero] at hh
 refine ⟨7,hh.congr fun i=>?_⟩; have h:=T.positive i; simp only [copaid,zpow_neg,zpow_ofNat, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]; have hv:(T.gap i:ℂ)≠0:= Complex.ofReal_ne_zero.mpr h.ne'; field_simp
end tests
variable {n:Side}{r:ℕ}(p:Players G r 6) (o:Full.Grid n r) (h:ℝ)(s:Fin r)
def echoSelf (B: Part G 6):= (∑ a:Who G 6,∑ b:Who G 6,(1/2:ℂ)*loot B a b*(↑(dues o h (s,a) (s,b)):ℂ))*ZeroR o h (air p s)
def echoesP (B: Part G 6) (f:At G r 6→At G r 6→ℝ):= ∑ i∈apart G 6 s,∑ j∈apart G 6 s,(∑ a:Who G 6,∑ b:Who G 6,(1/2:ℂ)*loot B a b*(↑(f (s,a) i*f (s,b) j):ℂ))*ZeroR o h (dict j (dict i (air p s)))
lemma quadPay (B:Part G 6)(hb:uncap B ∈ Reel G): ZeroR o h (update p s B)=echoSelf p o h s B+echoesP p o h s B (dues o h):=by
 obtain ⟨L,H⟩:=pays_slot p s o h
 rw [←H]; nth_rw 1 [cash_quad B (coin_caps _ hb)]; simp_rw [_root_.map_sum L, C_mul',L.map_smul,smul_eq_mul,H,gives_two,mul_add,Finset.sum_add_distrib]; unfold echoSelf echoesP; simp_rw [Finset.sum_mul,mul_assoc,Finset.mul_sum]
 congr 1; conv_lhs=> arg 2; intro s; rw [Finset.sum_comm]; arg 2; intro t; rw [Finset.sum_comm]
 conv_lhs=> rw [Finset.sum_comm]; arg 2; intro s; rw [Finset.sum_comm]
lemma carryPay (Z:Pack F)(k:E F 6): let l:= carryR n h Z; let B:=cloak F ((twistC h Z).val k); ZeroR o h (update p s (cloak F (l.val k)))=currency F n h k*ZeroR o h (air p s)+ echoSelf p o h s B +echoesP p o h s B (dues o h):=by
 intro l B; rw [show cloak F (l.val k)= B + currency F n h k • (1:Part G 6) from ?_]
 · obtain ⟨L,H⟩:=pays_slot p s o h; rw [←H,map_add,map_smul,H,H,quadPay p o h s B (by unfold B; rw [stretch]; exact (suitsP _).sees _)]; unfold air; simp only [smul_eq_mul]; abel
 change robes F 6 ((Outfit (twistC h Z)).val k+(sleeve F n h).val k)=_; rw [sleeve_eq,map_add,map_smul,robes_eq,robes_eq,unit_leg]; rfl
end YM.RG11.FirstW.Deck
