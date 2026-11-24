import YM.MS.Menus.Bulk
/-!
# The one token of the gauge algebra

Born s field. No gauge group rank assumption; availability of nonzero F11 uses nonabelian.
 Sign matches leading α from `Tuning`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect Detect.Mark Wire
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} (i j k l:CI G)
-- actual Lie value with s0,c. ∆.
lemma token4 : token (LE G 4) i j k=token (run (Wilsonian.W G)) i j k:= by
   let w:= [S i 0,C j 0,C k 0]; change (skin _ 4 _ w)=_
   have hv : ∀ (u:ℝ),sail (ray w) u=w:= by unfold w; simp [Detect.S,C,qnote]
   rw [skin_eq (j:=0) _ _ _ (by norm_num [w,fieldDim,wfield,dim,Detect.S,C,qnote,gaugeC,ghost]), torch_at]; simp only [hv,reading,iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one,one_smul]; unfold Top core; rw [enough w (h:=3) (by simp [w])]; rw [Pi.add_apply,map_add,Pi.add_apply] -- map_add interacts masks; fix
   unfold Book.levels; rw [Tone.grade,Tone.grade,enough w (by simp [w]),strange w (by simp [w]),add_zero]; -- finish
lemma freetip (m:PlaqAxes) (u:List (Lane4 G)): run (art (loadC idRail ((0:Cover),m)) gone) (S i 0 :: u) =0:= by
    unfold run Sew.art; rw [study]; let T := fun q:Axis×Conn G=> knot (loadC idRail ((0:Cover),m)) q; rw [deriv_lum (s:=Finset.univ (α:=Axis×Conn G)) _ _ _ (by rw [Finset.coe_univ]; exact Uses.entire _)]; -- edit
    apply Finset.sum_eq_zero; intro t ht; rw [show paywave _ _=0 from (by simp [paywave,way,gaugeC,knot,formAt,Landau.gauge]), zero_mul]
lemma palo (a:Atom Axis): paywave ((a,i),0) ((a,j),(0:Cover))=(if i=j then 1 else 0):= by by_cases he:i=j <;> simp [paywave,way,he]
lemma cargo (i:CI G): run (cog 0 i) [C j 0,C k 0]= -(letterLie j k i:ℂ):= by
    simp only [cog,map_sum,map_smul,Finset.sum_apply, Pi.smul_apply]; simp_rw [roles _ _ (GH _ 0) (GH _ 0) (logo0 ..) (logo0 ..),GH];
    simp only [C,qnote,ghostAt,pulse,palo]; change ∑ a,∑ b,(-(letterLie a b i:ℂ)/2)*_= _;
 
    simp [field, Landau.parity, Landau.p, cross,mul_add,Finset.sum_add_distrib,mul_ite]; rw [scaled_tensor,scaled_tensor, Only.ad_anti (baseC k),inner_neg_left]; push_cast; ring
lemma source_W (p: Dot G Cover)(x:LightMode G Cover)(a b c:Lane4 G): run (couple DotFlip (Cylinder.single x) p) [a,b,c]= paywave a x * run p [b,c]+ cross (DotFlip a) (DotFlip b) * paywave b x * run p [a,c]+ cross (DotFlip a) (DotFlip c)*cross (DotFlip b) (DotFlip c)*paywave c x*run p [a,b]:= by
   rw [wave_cost,scattered]; let T:=fun x:LightMode G Cover=>run (Cylinder.single x); have hp i j (w:List (Lane4 G)): T x (i::j::w)=0:= by unfold T; rw [D_eval i (run _),run,names]; simp [coin];
   change scatter _ _ (fun l r=>T x l* _)=_
   simp_rw [scatter_cons,scatter_nil,hp]; simp [T,logo0,pulse]; ring
lemma token_R : token (LE G 4) i j k=(LieColor i j k:ℂ):= by
   rw [token4]; let w:=[S i 0,C j 0,C k 0]; change run _ w=_; simp only [Wilsonian.W,bosons,ropes, AHplus,GHplus,weightW, map_add,map_sub,map_sum,Finset.sum_apply,Pi.add_apply,Pi.sub_apply]; simp_rw [show w=S i 0::C j 0::[C k 0] from rfl, freetip, source_W,cargo];
   simp [Detect.S,C,qnote,paywave,way,gaugeC,anti,ghost] -- sign net
   rw [show ((G.ad (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)).ofLp k=letterLie i j k from by simp [letterLie,baseC]]; simp_rw [scaled_tensor,← Only.rotate (baseC i) (baseC j) (baseC k)]
end YM.MS.Menus
