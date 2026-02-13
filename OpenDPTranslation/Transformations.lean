import OpenDPTranslation.Domains

structure Transformation (InputRowType OutputType : Type) [LE InputRowType] [LE OutputType] where
  input_domain : VectorDomain (AtomDomain InputRowType)
  output_domain : AtomDomain OutputType
  apply : List InputRowType → Except String OutputType

structure RowByRowTransformation (TA : Type) [LE TA] where
  input_domain : VectorDomain (AtomDomain TA)
  output_domain : AtomDomain TA
  apply : List TA → Except String (List TA)

structure RowByRowTransformationCross (TIA TOA : Type) [LE TIA] [LE TOA] where
  input_domain : VectorDomain (AtomDomain TIA)
  output_domain : AtomDomain TOA
  apply : List TIA → Except String (List TOA)

structure ScalarToVectorTransformation (T : Type) [LE T] where
  input_domain : AtomDomain T
  output_domain : VectorDomain (AtomDomain T)
  apply : T → Except String (List T)
