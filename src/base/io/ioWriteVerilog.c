/**CFile****************************************************************

  FileName    [ioWriteVerilog.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to output a special subset of Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteVerilog.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ioAbc.h"
#include "base/main/main.h"
#include "map/mio/mio.h"
#include "map/if/if.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Io_WriteVerilogInt( FILE * pFile, Abc_Ntk_t * pNtk, int fOnlyAnds, int fNewInterface );
static void Io_WriteVerilogPis( FILE * pFile, Abc_Ntk_t * pNtk, int Start );
static void Io_WriteVerilogPos( FILE * pFile, Abc_Ntk_t * pNtk, int Start, int fNewInterface );
static void Io_WriteVerilogAssigns( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_WriteVerilogWires( FILE * pFile, Abc_Ntk_t * pNtk, int Start );
static void Io_WriteVerilogRegs( FILE * pFile, Abc_Ntk_t * pNtk, int Start );
static void Io_WriteVerilogLatches( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_WriteVerilogObjects( FILE * pFile, Abc_Ntk_t * pNtk, int fOnlyAnds );
static int  Io_WriteVerilogWiresCount( Abc_Ntk_t * pNtk );
static char * Io_WriteVerilogGetName( char * pName );
static int Io_WriteVerilogNodesHaveSameFanins( Abc_Obj_t * pNode, Abc_Obj_t * pNode2 );
static int Io_WriteVerilogIsPrevTwinNode( Abc_Obj_t * pNode );
static int Io_WriteVerilogLutHasDualAttrs( Abc_Ntk_t * pNtk );
static void Io_WriteVerilogLutTransferDualAttrs( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkTemp );
static If_DualAttr_t * Io_WriteVerilogObjDualAttr( Abc_Obj_t * pObj );

static void Io_WriteVerilogDualAttrFree( void * pMan, void * pObj )
{
    (void)pMan;
    ABC_FREE( pObj );
}

static int Io_WriteVerilogLutHasDualAttrs( Abc_Ntk_t * pNtk )
{
    return pNtk && pNtk->vAttrs && Vec_PtrEntry(pNtk->vAttrs, VEC_ATTR_DATA1) != NULL;
}

static If_DualAttr_t * Io_WriteVerilogObjDualAttr( Abc_Obj_t * pObj )
{
    Vec_Att_t * pAttrs;
    if ( pObj == NULL || pObj->pNtk == NULL || pObj->pNtk->vAttrs == NULL )
        return NULL;
    pAttrs = (Vec_Att_t *)Vec_PtrEntry( pObj->pNtk->vAttrs, VEC_ATTR_DATA1 );
    return pAttrs ? (If_DualAttr_t *)Vec_AttEntry( pAttrs, pObj->Id ) : NULL;
}

static Abc_Obj_t * Io_WriteVerilogLutFindTempNetByName( Abc_Ntk_t * pNtkTemp, const char * pName )
{
    Abc_Obj_t * pNet;
    char Buffer[1000];
    if ( pName == NULL )
        return NULL;
    pNet = Abc_NtkFindNet( pNtkTemp, (char *)pName );
    if ( pNet )
        return pNet;
    sprintf( Buffer, "new_%s", pName );
    return Abc_NtkFindNet( pNtkTemp, Buffer );
}

static Abc_Obj_t * Io_WriteVerilogLutMapTempNet( Abc_Ntk_t * pNtkTemp, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pCopy, * pNet;
    if ( pObj == NULL )
        return NULL;
    pCopy = (Abc_Obj_t *)pObj->pCopy;
    if ( pCopy && pCopy->pCopy )
        return (Abc_Obj_t *)pCopy->pCopy;
    if ( pCopy && Abc_ObjIsNet(pCopy) )
        return pCopy;
    if ( pCopy && Abc_ObjFanoutNum(pCopy) > 0 && Abc_ObjIsNet(Abc_ObjFanout0(pCopy)) )
        return Abc_ObjFanout0(pCopy);
    pNet = Io_WriteVerilogLutFindTempNetByName( pNtkTemp, Abc_ObjName(pObj) );
    if ( pNet )
        return pNet;
    if ( Abc_ObjFanoutNum(pObj) > 0 )
        return Io_WriteVerilogLutFindTempNetByName( pNtkTemp, Abc_ObjName(Abc_ObjFanout0(pObj)) );
    return NULL;
}

static void Io_WriteVerilogLutTransferDualAttrs( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkTemp )
{
    Vec_Att_t * pAttrsOld, * pAttrsNew;
    Abc_Obj_t * pObj, * pMate;
    If_DualAttr_t * pOld, * pNew;
    int i, k;
    if ( !Io_WriteVerilogLutHasDualAttrs(pNtk) )
        return;
    /* write_verilog -K may build a temporary SOP/netlist view before printing
       LUT instances.  The dual-pair metadata is stored on ABC objects, so it
       has to follow each node through pCopy into this temporary network. */
    pAttrsOld = (Vec_Att_t *)Vec_PtrEntry( pNtk->vAttrs, VEC_ATTR_DATA1 );
    pAttrsNew = Vec_AttAlloc( Abc_NtkObjNumMax(pNtkTemp) + 1, NULL, NULL, NULL, Io_WriteVerilogDualAttrFree );
    Vec_PtrWriteEntry( pNtkTemp->vAttrs, VEC_ATTR_DATA1, pAttrsNew );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pOld = (If_DualAttr_t *)Vec_AttEntry( pAttrsOld, pObj->Id );
        if ( pOld == NULL || pObj->pCopy == NULL )
            continue;
        pMate = Abc_NtkObj( pNtk, pOld->iMate );
        if ( pMate == NULL || pMate->pCopy == NULL )
            continue;
        pNew = ABC_CALLOC( If_DualAttr_t, 1 );
        pNew->iMate = ((Abc_Obj_t *)pMate->pCopy)->Id;
        pNew->nLutSize = pOld->nLutSize;
        pNew->nLeaves = pOld->nLeaves;
        pNew->uTruth0 = pOld->uTruth0;
        pNew->uTruth1 = pOld->uTruth1;
        for ( k = 0; k < pOld->nLeaves; k++ )
        {
            Abc_Obj_t * pLeaf = Abc_NtkObj( pNtk, pOld->pLeaves[k] );
            Abc_Obj_t * pLeafNet = Io_WriteVerilogLutMapTempNet( pNtkTemp, pLeaf );
            if ( pLeafNet == NULL )
                break;
            pNew->pLeaves[k] = pLeafNet->Id;
        }
        if ( k != pOld->nLeaves )
        {
            ABC_FREE( pNew );
            continue;
        }
        Vec_AttWriteEntry( pAttrsNew, ((Abc_Obj_t *)pObj->pCopy)->Id, pNew );
    }
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Write verilog.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilog( Abc_Ntk_t * pNtk, char * pFileName, int fOnlyAnds, int fNewInterface )
{
    Abc_Ntk_t * pNetlist;
    FILE * pFile;
    int i;
    
    // can only write nodes represented using local AIGs
    if ( !Abc_NtkIsAigNetlist(pNtk) && !Abc_NtkIsMappedNetlist(pNtk) )
    {
        printf( "Io_WriteVerilog(): Can produce Verilog for mapped or AIG netlists only.\n" );
        return;
    }
    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteVerilog(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    // write the equations for the network
    fprintf( pFile, "// Benchmark \"%s\" written by ABC on %s\n", pNtk->pName, Extra_TimeStamp() );
    fprintf( pFile, "\n" );

    // write modules
    if ( pNtk->pDesign )
    {
        // write the network first
        Io_WriteVerilogInt( pFile, pNtk, fOnlyAnds, fNewInterface );
        // write other things
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pNetlist, i )
        {
            assert( Abc_NtkIsNetlist(pNetlist) );
            if ( pNetlist == pNtk )
                continue;
            fprintf( pFile, "\n" );
            Io_WriteVerilogInt( pFile, pNetlist, fOnlyAnds, fNewInterface );
        }
    }
    else
    {
        Io_WriteVerilogInt( pFile, pNtk, fOnlyAnds, fNewInterface );
    }

    fprintf( pFile, "\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Writes verilog.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogInt( FILE * pFile, Abc_Ntk_t * pNtk, int fOnlyAnds, int fNewInterface )
{
    // write inputs and outputs
//    fprintf( pFile, "module %s ( gclk,\n   ", Abc_NtkName(pNtk) );
    fprintf( pFile, "module %s ( ", Io_WriteVerilogGetName(Abc_NtkName(pNtk)) );
    // add the clock signal if it does not exist
    if ( Abc_NtkLatchNum(pNtk) > 0 && Nm_ManFindIdByName(pNtk->pManName, "clock", ABC_OBJ_PI) == -1 )
        fprintf( pFile, "clock, " );
    // write other primary inputs
    fprintf( pFile, "\n   " );
    if ( Abc_NtkPiNum(pNtk) > 0  )
    {
        Io_WriteVerilogPis( pFile, pNtk, 3 );
        fprintf( pFile, ",\n   " );
    }
    if ( Abc_NtkPoNum(pNtk) > 0  )
        Io_WriteVerilogPos( pFile, pNtk, 3, fNewInterface );
    fprintf( pFile, "  );\n" );
    // add the clock signal if it does not exist
    if ( Abc_NtkLatchNum(pNtk) > 0 && Nm_ManFindIdByName(pNtk->pManName, "clock", ABC_OBJ_PI) == -1 )
        fprintf( pFile, "  input  clock;\n" );
    // write inputs, outputs, registers, and wires
    if ( Abc_NtkPiNum(pNtk) > 0  )
    {
//        fprintf( pFile, "  input gclk," );
        fprintf( pFile, "  input " );
        Io_WriteVerilogPis( pFile, pNtk, 10 );
        fprintf( pFile, ";\n" );
    }
    if ( Abc_NtkPoNum(pNtk) > 0  )
    {
        fprintf( pFile, "  output" );
        Io_WriteVerilogPos( pFile, pNtk, 5, fNewInterface );
        fprintf( pFile, ";\n" );
    }
    // if this is not a blackbox, write internal signals
    if ( !Abc_NtkHasBlackbox(pNtk) )
    {
        if ( Abc_NtkLatchNum(pNtk) > 0 )
        {
            fprintf( pFile, "  reg" );
            Io_WriteVerilogRegs( pFile, pNtk, 4 );
            fprintf( pFile, ";\n" );
        }
        if ( Io_WriteVerilogWiresCount(pNtk) > 0 )
        {
            fprintf( pFile, "  wire" );
            Io_WriteVerilogWires( pFile, pNtk, 4 );
            fprintf( pFile, ";\n" );
        }
        // write nodes
        Io_WriteVerilogObjects( pFile, pNtk, fOnlyAnds );        
        // write registers
        if ( Abc_NtkLatchNum(pNtk) > 0 )
            Io_WriteVerilogLatches( pFile, pNtk );
    }
    if ( fNewInterface )
        Io_WriteVerilogAssigns( pFile, pNtk );
    // finalize the file
    fprintf( pFile, "endmodule\n\n" );
} 

/**Function*************************************************************

  Synopsis    [Writes the primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogPis( FILE * pFile, Abc_Ntk_t * pNtk, int Start )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachPi( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanout0(pTerm);
        // get the line length after this name is written
        AddedLength = strlen(Io_WriteVerilogGetName(Abc_ObjName(pNet))) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Io_WriteVerilogGetName(Abc_ObjName(pNet)), (i==Abc_NtkPiNum(pNtk)-1)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
} 

/**Function*************************************************************

  Synopsis    [Writes the primary outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogPos( FILE * pFile, Abc_Ntk_t * pNtk, int Start, int fNewInterface )
{
    Abc_Obj_t * pTerm, * pNet, * pSkip;
    char Name[100], * pName = Name;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;
    int nskip;

    pSkip = 0;
    nskip = 0;

    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachPo( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanin0(pTerm);
        
        if ( Abc_ObjIsPi(Abc_ObjFanin0(pNet)) )
        {
            // Skip this output since it is a feedthrough -- the same
            // name will appear as an input and an output which other
            // tools reading verilog do not like.
            
            nskip++;
            pSkip = pNet;   // save an example of skipped net
            continue;
        }
        
        // get the line length after this name is written
        if ( fNewInterface )
            sprintf( Name, "po_username%d", i );
        else
            pName = Abc_ObjName(pNet);
        AddedLength = strlen(Io_WriteVerilogGetName(pName)) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Io_WriteVerilogGetName(pName), (i==Abc_NtkPoNum(pNtk)-1)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }

    if (nskip != 0)
    {
        assert (pSkip);
        printf( "Io_WriteVerilogPos(): Omitted %d feedthrough nets from output list of module (e.g. %s).\n", nskip, Abc_ObjName(pSkip) );
        return;
    }

}

/**Function*************************************************************

  Synopsis    [Writes the primary outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAssigns( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pTerm, * pNet, * pSkip;
    int i;
    Abc_NtkForEachPo( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanin0(pTerm);
        if ( Abc_ObjIsPi(Abc_ObjFanin0(pNet)) )
        {
            // Skip this output since it is a feedthrough -- the same
            // name will appear as an input and an output which other
            // tools reading verilog do not like.
            
            pSkip = pNet;   // save an example of skipped net
            continue;
        }
        fprintf( pFile, "  assign po_username%d = %s;\n", i, Abc_ObjName(pNet) );
    }
}

/**Function*************************************************************

  Synopsis    [Writes the wires.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogWires( FILE * pFile, Abc_Ntk_t * pNtk, int Start )
{
    Abc_Obj_t * pObj, * pNet, * pBox, * pTerm;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i, k, Counter, nNodes;

    // count the number of wires
    nNodes = Io_WriteVerilogWiresCount( pNtk );

    // write the wires
    Counter = 0;
    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( i == 0 ) 
            continue;
        pNet = Abc_ObjFanout0(pObj);
        if ( Abc_ObjFanoutNum(pNet) > 0 && Abc_ObjIsCo(Abc_ObjFanout0(pNet)) )
            continue;
        Counter++;
        // get the line length after this name is written
        AddedLength = strlen(Io_WriteVerilogGetName(Abc_ObjName(pNet))) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Io_WriteVerilogGetName(Abc_ObjName(pNet)), (Counter==nNodes)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        pNet = Abc_ObjFanin0(Abc_ObjFanin0(pObj));
        Counter++;
        // get the line length after this name is written
        AddedLength = strlen(Io_WriteVerilogGetName(Abc_ObjName(pNet))) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Io_WriteVerilogGetName(Abc_ObjName(pNet)), (Counter==nNodes)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
    Abc_NtkForEachBox( pNtk, pBox, i )
    {
        if ( Abc_ObjIsLatch(pBox) )
            continue;
        Abc_ObjForEachFanin( pBox, pTerm, k )
        {
            pNet = Abc_ObjFanin0(pTerm);
            Counter++;
            // get the line length after this name is written
            AddedLength = strlen(Io_WriteVerilogGetName(Abc_ObjName(pNet))) + 2;
            if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, "\n   " );
                // reset the line length
                LineLength  = 3;
                NameCounter = 0;
            }
            fprintf( pFile, " %s%s", Io_WriteVerilogGetName(Abc_ObjName(pNet)), (Counter==nNodes)? "" : "," );
            LineLength += AddedLength;
            NameCounter++;
        }
        Abc_ObjForEachFanout( pBox, pTerm, k )
        {
            pNet = Abc_ObjFanout0(pTerm);
            if ( Abc_ObjFanoutNum(pNet) > 0 && Abc_ObjIsCo(Abc_ObjFanout0(pNet)) )
                continue;
            Counter++;
            // get the line length after this name is written
            AddedLength = strlen(Io_WriteVerilogGetName(Abc_ObjName(pNet))) + 2;
            if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, "\n   " );
                // reset the line length
                LineLength  = 3;
                NameCounter = 0;
            }
            fprintf( pFile, " %s%s", Io_WriteVerilogGetName(Abc_ObjName(pNet)), (Counter==nNodes)? "" : "," );
            LineLength += AddedLength;
            NameCounter++;
        }
    }
    assert( Counter == nNodes );
}

/**Function*************************************************************

  Synopsis    [Writes the regs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogRegs( FILE * pFile, Abc_Ntk_t * pNtk, int Start )
{
    Abc_Obj_t * pLatch, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i, Counter, nNodes;

    // count the number of latches
    nNodes = Abc_NtkLatchNum(pNtk);

    // write the wires
    Counter = 0;
    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        pNet = Abc_ObjFanout0(Abc_ObjFanout0(pLatch));
        Counter++;
        // get the line length after this name is written
        AddedLength = strlen(Io_WriteVerilogGetName(Abc_ObjName(pNet))) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Io_WriteVerilogGetName(Abc_ObjName(pNet)), (Counter==nNodes)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
}

/**Function*************************************************************

  Synopsis    [Writes the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogLatches( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch;
    int i;
    if ( Abc_NtkLatchNum(pNtk) == 0 )
        return;
    // write the latches
//    fprintf( pFile, "  always @(posedge %s) begin\n", Io_WriteVerilogGetName(Abc_ObjFanout0(Abc_NtkPi(pNtk,0))) );
//    fprintf( pFile, "  always begin\n" );
    fprintf( pFile, "  always @ (posedge clock) begin\n" );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        fprintf( pFile, "    %s", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(Abc_ObjFanout0(pLatch)))) );
        fprintf( pFile, " <= %s;\n", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin0(Abc_ObjFanin0(pLatch)))) );
    }
    fprintf( pFile, "  end\n" );
    // check if there are initial values
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        if ( Abc_LatchInit(pLatch) == ABC_INIT_ZERO || Abc_LatchInit(pLatch) == ABC_INIT_ONE )
            break;
    if ( i == Abc_NtkLatchNum(pNtk) )
        return;
    // write the initial values
    fprintf( pFile, "  initial begin\n" );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        if ( Abc_LatchInit(pLatch) == ABC_INIT_ZERO )
            fprintf( pFile, "    %s <= 1\'b0;\n", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(Abc_ObjFanout0(pLatch)))) );
        else if ( Abc_LatchInit(pLatch) == ABC_INIT_ONE )
            fprintf( pFile, "    %s <= 1\'b1;\n", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(Abc_ObjFanout0(pLatch)))) );
    }
    fprintf( pFile, "  end\n" );
}

/**Function*************************************************************

  Synopsis    [Checks whether two mapped nodes have the same fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Io_WriteVerilogNodesHaveSameFanins( Abc_Obj_t * pNode, Abc_Obj_t * pNode2 )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( Abc_ObjFaninNum(pNode) != Abc_ObjFaninNum(pNode2) )
        return 0;
    Abc_ObjForEachFanin( pNode, pFanin, i )
        if ( pFanin != Abc_ObjFanin(pNode2, i) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks whether this mapped node is the second output of a twin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Io_WriteVerilogIsPrevTwinNode( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pPrev;
    Mio_Gate_t * pGate = (Mio_Gate_t *)pNode->pData;
    if ( pGate == NULL || Mio_GateReadTwin(pGate) == NULL || Abc_ObjId(pNode) == 0 )
        return 0;
    pPrev = Abc_NtkObj( pNode->pNtk, Abc_ObjId(pNode) - 1 );
    if ( pPrev == NULL || !Abc_ObjIsNode(pPrev) )
        return 0;
    if ( Mio_GateReadTwin(pGate) != (Mio_Gate_t *)pPrev->pData )
        return 0;
    return Io_WriteVerilogNodesHaveSameFanins( pPrev, pNode );
}

/**Function*************************************************************

  Synopsis    [Writes the nodes and boxes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogObjects( FILE * pFile, Abc_Ntk_t * pNtk, int fOnlyAnds )
{
    int fUseSimpleGateNames = 0;
    Vec_Vec_t * vLevels;
    Abc_Ntk_t * pNtkBox;
    Abc_Obj_t * pObj, * pTerm, * pFanin;
    Hop_Obj_t * pFunc;
    int i, k, Counter, nDigits, Length;

    // write boxes
    nDigits = Abc_Base10Log( Abc_NtkBoxNum(pNtk)-Abc_NtkLatchNum(pNtk) );
    Counter = 0;
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        if ( Abc_ObjIsLatch(pObj) )
            continue;
        pNtkBox = (Abc_Ntk_t *)pObj->pData;
        fprintf( pFile, "  %s box%0*d", pNtkBox->pName, nDigits, Counter++ );
        fprintf( pFile, "(" );
        Abc_NtkForEachPi( pNtkBox, pTerm, k )
        {
            fprintf( pFile, ".%s",   Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pTerm))) );
            fprintf( pFile, "(%s), ", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin0(Abc_ObjFanin(pObj,k)))) );
        }
        Abc_NtkForEachPo( pNtkBox, pTerm, k )
        {
            fprintf( pFile, ".%s",   Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin0(pTerm))) );
            fprintf( pFile, "(%s)%s", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(Abc_ObjFanout(pObj,k)))), k==Abc_NtkPoNum(pNtkBox)-1? "":", " );
        }
        fprintf( pFile, ");\n" );
    }
    // write nodes
    if ( Abc_NtkHasMapping(pNtk) )
    {
        Length  = Mio_LibraryReadGateNameMax((Mio_Library_t *)pNtk->pManFunc);
        nDigits = Abc_Base10Log( Abc_NtkNodeNum(pNtk) );
        Counter = 0;
        Abc_NtkForEachNode( pNtk, pObj, k )
        {
            Mio_Gate_t * pGate = (Mio_Gate_t *)pObj->pData;
            Abc_Obj_t * pNode2 = NULL;
            Mio_Pin_t * pGatePin;
            if ( Io_WriteVerilogIsPrevTwinNode( pObj ) )
                continue;
            if ( Abc_ObjFaninNum(pObj) == 0 && (!strcmp(Mio_GateReadName(pGate), "_const0_") || !strcmp(Mio_GateReadName(pGate), "_const1_")) )
            {
                fprintf( pFile, "  %-*s %s = 1\'b%d;\n", Length, "assign", Io_WriteVerilogGetName(Abc_ObjName( Abc_ObjFanout0(pObj) )), !strcmp(Mio_GateReadName(pGate), "_const1_") );
                continue;
            }
            pNode2 = Abc_NtkFetchTwinNode( pObj );
            if ( pNode2 && !Io_WriteVerilogNodesHaveSameFanins( pObj, pNode2 ) )
                pNode2 = NULL;
            // write the node
            if ( fUseSimpleGateNames )
            {
                fprintf( pFile, "%-*s ", Length, Mio_GateReadName(pGate) );
                fprintf( pFile, "( %s", Io_WriteVerilogGetName(Abc_ObjName( Abc_ObjFanout0(pObj) )) );
                for ( pGatePin = Mio_GateReadPins(pGate), i = 0; pGatePin; pGatePin = Mio_PinReadNext(pGatePin), i++ )
                    fprintf( pFile, ", %s", Io_WriteVerilogGetName(Abc_ObjName( Abc_ObjFanin(pObj,i) )) );
                assert ( i == Abc_ObjFaninNum(pObj) );
                fprintf( pFile, " );\n" );
            }
            else
            {
                fprintf( pFile, "  %-*s g%0*d", Length, Mio_GateReadName(pGate), nDigits, Counter++ );
                fprintf( pFile, "(" );
                for ( pGatePin = Mio_GateReadPins(pGate), i = 0; pGatePin; pGatePin = Mio_PinReadNext(pGatePin), i++ )
                {
                    fprintf( pFile, ".%s", Io_WriteVerilogGetName(Mio_PinReadName(pGatePin)) );
                    fprintf( pFile, "(%s), ", Io_WriteVerilogGetName(Abc_ObjName( Abc_ObjFanin(pObj,i) )) );
                }
                assert ( i == Abc_ObjFaninNum(pObj) );
                fprintf( pFile, ".%s", Io_WriteVerilogGetName(Mio_GateReadOutName(pGate)) );
                fprintf( pFile, "(%s)", Io_WriteVerilogGetName(Abc_ObjName( Abc_ObjFanout0(pObj) )) );
                if ( pNode2 )
                {
                    fprintf( pFile, ", " );
                    fprintf( pFile, ".%s", Io_WriteVerilogGetName(Mio_GateReadOutName((Mio_Gate_t *)pNode2->pData)) );
                    fprintf( pFile, "(%s)", Io_WriteVerilogGetName(Abc_ObjName( Abc_ObjFanout0(pNode2) )) );
                }
                fprintf( pFile, ");\n" );
            }
        }
    }
    else
    {
        //Vec_Int_t * vMap = Vec_IntStartFull( 2*Abc_NtkObjNumMax(pNtk) );
        vLevels = Vec_VecAlloc( 10 );
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            if ( Abc_ObjFaninNum(pObj) == 0 )
            {
                fprintf( pFile, "  assign %s = ", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
                fprintf( pFile, "1\'b%d;\n", Abc_NodeIsConst1(pObj) );
                continue;
            }
            /*
            if ( Abc_ObjFaninNum(pObj) == 1 || Abc_ObjIsCo(Abc_ObjFanout0(Abc_ObjFanout0(pObj))) )
            {
                int iLit = Abc_Var2Lit( Abc_ObjId( Abc_ObjFanin0(Abc_ObjFanin0(pObj)) ), Abc_NodeIsInv(pObj) );
                int iObj = Vec_IntEntry( vMap, iLit );
                if ( iObj == -1 )
                    Vec_IntWriteEntry( vMap, iLit, Abc_ObjId(Abc_ObjFanout0(pObj)) );
                else
                {
                    fprintf( pFile, "  assign %s = ", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
                    fprintf( pFile, "%s;\n", Io_WriteVerilogGetName(Abc_ObjName(Abc_NtkObj(pNtk, iObj))) );
                    continue;
                }
            }
            */
            pFunc = (Hop_Obj_t *)pObj->pData;
            fprintf( pFile, "  assign %s = ", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
            // set the input names
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Hop_IthVar((Hop_Man_t *)pNtk->pManFunc, k)->pData = Extra_UtilStrsav(Io_WriteVerilogGetName(Abc_ObjName(pFanin)));
            // write the formula
            Hop_ObjPrintVerilog( pFile, pFunc, vLevels, 0, fOnlyAnds );
            if ( pObj->fPersist )
            {
                Abc_Obj_t * pFan0 = Abc_ObjFanin0(Abc_ObjFanin(pObj, 0));
                Abc_Obj_t * pFan1 = Abc_ObjFanin0(Abc_ObjFanin(pObj, 1));
                int Cond = Abc_ObjIsNode(pFan0) && Abc_ObjIsNode(pFan1) && !pFan0->fPersist && !pFan1->fPersist;
                fprintf( pFile, "; // MUXF7 %s\n", Cond ? "":"to be legalized" );
            }
            else
            fprintf( pFile, ";\n" );
            // clear the input names
            Abc_ObjForEachFanin( pObj, pFanin, k )
                ABC_FREE( Hop_IthVar((Hop_Man_t *)pNtk->pManFunc, k)->pData );
        }
        Vec_VecFree( vLevels );
        //Vec_IntFree( vMap );
    }
}

/**Function*************************************************************

  Synopsis    [Counts the number of wires.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteVerilogWiresCount( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pNet, * pBox;
    int i, k, nWires;
    nWires = Abc_NtkLatchNum(pNtk);
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( i == 0 ) 
            continue;
        pNet = Abc_ObjFanout0(pObj);
        if ( Abc_ObjFanoutNum(pNet) > 0 && Abc_ObjIsCo(Abc_ObjFanout0(pNet)) )
            continue;
        nWires++;
    }
    Abc_NtkForEachBox( pNtk, pBox, i )
    {
        if ( Abc_ObjIsLatch(pBox) )
            continue;
        nWires += Abc_ObjFaninNum(pBox);
        Abc_ObjForEachFanout( pBox, pObj, k )
        {
            pNet = Abc_ObjFanout0(pObj);
            if ( Abc_ObjFanoutNum(pNet) > 0 && Abc_ObjIsCo(Abc_ObjFanout0(pNet)) )
                continue;
            nWires++;
        }
    }
    return nWires;
}

/**Function*************************************************************

  Synopsis    [Prepares the name for writing the Verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Io_WriteVerilogGetName( char * pName )
{
    static char Buffer[500];
    int i, Length = strlen(pName);
    if ( pName[0] < '0' || pName[0] > '9' )
    {
        for ( i = 0; i < Length; i++ )
            if ( !((pName[i] >= 'a' && pName[i] <= 'z') || 
                 (pName[i] >= 'A' && pName[i] <= 'Z') || 
                 (pName[i] >= '0' && pName[i] <= '9') || pName[i] == '_') )
                 break;
        if ( i == Length )
            return pName;
    }
    // create Verilog style name
    Buffer[0] = '\\';
    for ( i = 0; i < Length; i++ )
        Buffer[i+1] = pName[i];
    Buffer[Length+1] = ' ';
    Buffer[Length+2] = 0;
    return Buffer;
}


/**Function*************************************************************

  Synopsis    [Write the network of K-input LUTs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteLutModule( FILE * pFile, int nLutSize )
{    
    fprintf( pFile, "module lut%d ( in, out );\n", nLutSize );
    fprintf( pFile, "    parameter TT = %d\'h0;\n", 1<<nLutSize );
    fprintf( pFile, "    input [%d:0] in;\n", nLutSize-1 );
    fprintf( pFile, "    output out;\n" );
    fprintf( pFile, "    assign out = TT[in];\n" );
    fprintf( pFile, "endmodule\n\n" );
}
void Io_WriteDualLutModule( FILE * pFile, int nLutSize )
{
    int nSmall = nLutSize - 1;
    fprintf( pFile, "module dual_lut%d ( in, z5, z );\n", nLutSize );
    fprintf( pFile, "    parameter TT_Z5 = %d\'h0;\n", 1 << nSmall );
    fprintf( pFile, "    parameter TT_Z = %d\'h0;\n", 1 << nSmall );
    fprintf( pFile, "    input [%d:0] in;\n", nLutSize - 1 );
    fprintf( pFile, "    output z5;\n" );
    fprintf( pFile, "    output z;\n" );
    fprintf( pFile, "    wire o0 = TT_Z5[in[%d:0]];\n", nSmall - 1 );
    fprintf( pFile, "    wire o1 = TT_Z[in[%d:0]];\n", nSmall - 1 );
    fprintf( pFile, "    assign z5 = o0;\n" );
    fprintf( pFile, "    assign z = o1;\n" );
    fprintf( pFile, "endmodule\n\n" );
}
void Io_WriteFixedModules( FILE * pFile )
{    
    fprintf( pFile, "module LUT6 #( parameter INIT = 64\'h0000000000000000 ) (\n" );
    fprintf( pFile, "    output O,\n" );
    fprintf( pFile, "    input I0,\n" );
    fprintf( pFile, "    input I1,\n" );
    fprintf( pFile, "    input I2,\n" );
    fprintf( pFile, "    input I3,\n" );
    fprintf( pFile, "    input I4,\n" );
    fprintf( pFile, "    input I5\n" );
    fprintf( pFile, ");\n" );
    fprintf( pFile, "    assign O = INIT[ {I5, I4, I3, I2, I1, I0} ];\n" );
    fprintf( pFile, "endmodule\n\n" );

    fprintf( pFile, "module MUXF7 (\n" );
    fprintf( pFile, "    output O,\n" );
    fprintf( pFile, "    input I0,\n" );
    fprintf( pFile, "    input I1,\n" );
    fprintf( pFile, "    input S\n" );
    fprintf( pFile, ");\n" );
    fprintf( pFile, "    assign O = S ? I1 : I0;\n" );
    fprintf( pFile, "endmodule\n\n" );

    fprintf( pFile, "module MUXF8 (\n" );
    fprintf( pFile, "    output O,\n" );
    fprintf( pFile, "    input I0,\n" );
    fprintf( pFile, "    input I1,\n" );
    fprintf( pFile, "    input S\n" );
    fprintf( pFile, ");\n" );
    fprintf( pFile, "    assign O = S ? I1 : I0;\n" );
    fprintf( pFile, "endmodule\n\n" );
}
void Io_WriteVerilogObjectsLut( FILE * pFile, Abc_Ntk_t * pNtk, int nLutSize, int fFixed )
{
    Abc_Ntk_t * pNtkBox;
    Abc_Obj_t * pObj, * pTerm;
    int i, k, Counter, nDigits, Length = 0;

    // write boxes
    nDigits = Abc_Base10Log( Abc_NtkBoxNum(pNtk)-Abc_NtkLatchNum(pNtk) );
    Counter = 0;
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        if ( Abc_ObjIsLatch(pObj) )
            continue;
        pNtkBox = (Abc_Ntk_t *)pObj->pData;
        fprintf( pFile, "  %s box%0*d", pNtkBox->pName, nDigits, Counter++ );
        fprintf( pFile, "(" );
        Abc_NtkForEachPi( pNtkBox, pTerm, k )
        {
            fprintf( pFile, ".%s",   Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pTerm))) );
            fprintf( pFile, "(%s), ", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin0(Abc_ObjFanin(pObj,k)))) );
        }
        Abc_NtkForEachPo( pNtkBox, pTerm, k )
        {
            fprintf( pFile, ".%s",   Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin0(pTerm))) );
            fprintf( pFile, "(%s)%s", Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(Abc_ObjFanout(pObj,k)))), k==Abc_NtkPoNum(pNtkBox)-1? "":", " );
        }
        fprintf( pFile, ");\n" );
    }

    // find the longest signal name
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        Length = Abc_MaxInt( Length, strlen(Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj)))) );
        Abc_ObjForEachFanin( pObj, pTerm, k )
            Length = Abc_MaxInt( Length, strlen(Io_WriteVerilogGetName(Abc_ObjName(pTerm))) );
    }

    // write LUT instances
    nDigits = Abc_Base10Log( Abc_NtkNodeNum(pNtk) );
    Counter = 0;
    if ( fFixed )
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( pObj->fPersist )
        {
            int One = Abc_ObjFanin0(Abc_ObjFanin(pObj, 1))->fPersist && Abc_ObjFanin0(Abc_ObjFanin(pObj, 2))->fPersist;
            fprintf( pFile, "  MUXF%d                       ", 7+One );
            fprintf( pFile, " mux_%0*d (", nDigits, Counter++ );
            fprintf( pFile, " %*s", Length, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
            for ( k = Abc_ObjFaninNum(pObj) - 1; k >= 0; k-- )
                fprintf( pFile, ", %*s", Length, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin(pObj, k))) );
            fprintf( pFile, " );\n" );
        }
        else
        {
            word Truth = Abc_SopToTruth( (char *)pObj->pData, Abc_ObjFaninNum(pObj) );
            fprintf( pFile, "  LUT6 #(64\'h" );
            fprintf( pFile, "%08x%08x", (unsigned)(Truth >> 32), (unsigned)Truth );
            fprintf( pFile, ") lut_%0*d (", nDigits, Counter++ );
            fprintf( pFile, " %*s", Length, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
            for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
                fprintf( pFile, ", %*s", Length, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin(pObj, k))) );
            for (      ; k < 6; k++ )
                fprintf( pFile, ", %*s", Length, "1\'b0" );
            fprintf( pFile, " );\n" );
        }
    }
    else
    {
    Vec_Int_t * vPrinted = Vec_IntStart( Abc_NtkObjNumMax(pNtk) + 1 );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        If_DualAttr_t * pDual = Io_WriteVerilogObjDualAttr( pObj );
        if ( Vec_IntEntry( vPrinted, pObj->Id ) )
            continue;
        if ( pDual )
        {
            Abc_Obj_t * pMate = Abc_NtkObj( pNtk, pDual->iMate );
            Abc_Obj_t * pFanins[IF_MAX_LUTSIZE];
            int nUnion = 0, m, nDigitsHex;
            char NameOut0[500], NameOut1[500];
            /* Be conservative at the writer boundary.  If the mate disappeared
               during temporary-network construction, or if both endpoints map
               to the same printable net, emit the current node as a normal LUT. */
            if ( pMate == pObj )
                goto IoWriteSingleLut;
            if ( pMate == NULL || !Abc_ObjIsNode(pMate) || pDual->nLutSize != nLutSize )
                goto IoWriteSingleLut;
            if ( Vec_IntEntry( vPrinted, pMate->Id ) )
                goto IoWriteSingleLut;
            if ( Abc_ObjFanout0(pObj) == Abc_ObjFanout0(pMate) )
                goto IoWriteSingleLut;
            if ( !strcmp( Abc_ObjName(Abc_ObjFanout0(pObj)), Abc_ObjName(Abc_ObjFanout0(pMate)) ) )
                goto IoWriteSingleLut;
            strcpy( NameOut0, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
            strcpy( NameOut1, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pMate))) );
            if ( !strcmp( NameOut0, NameOut1 ) )
                goto IoWriteSingleLut;
            nUnion = pDual->nLeaves;
            for ( k = 0; k < nUnion; k++ )
            {
                pFanins[k] = Abc_NtkObj( pNtk, pDual->pLeaves[k] );
                if ( pFanins[k] == NULL )
                    goto IoWriteSingleLut;
            }
            /* The hardware model is two (N-1)-input LUTs sharing the same data
               inputs plus a fixed select input.  Larger unions are outside the
               implemented simple dual-output case. */
            if ( nUnion > nLutSize - 1 )
                goto IoWriteSingleLut;
            /* The mapper has already simulated the two accepted cones over this
               union-leaf order, so the writer only serializes the stored TT. */
            nDigitsHex = Abc_MaxInt( 1, 1 << (nLutSize - 3) );
            fprintf( pFile, "  dual_lut%d #(%d\'h%0*llx, %d\'h%0*llx) dual_%0*d ( {", nLutSize,
                1 << (nLutSize - 1), nDigitsHex, (unsigned long long)pDual->uTruth0,
                1 << (nLutSize - 1), nDigitsHex, (unsigned long long)pDual->uTruth1, nDigits, Counter++ );
            fprintf( pFile, "%*s", Length, "1\'b1" );
            for ( m = nLutSize - 2; m >= nUnion; m-- )
                fprintf( pFile, ", %*s", Length, "1\'b0" );
            for ( m = nUnion - 1; m >= 0; m-- )
                fprintf( pFile, ", %*s", Length, Io_WriteVerilogGetName(Abc_ObjName(pFanins[m])) );
            fprintf( pFile, "}, %*s, %*s );\n", Length, NameOut0, Length, NameOut1 );
            Vec_IntWriteEntry( vPrinted, pObj->Id, 1 );
            Vec_IntWriteEntry( vPrinted, pMate->Id, 1 );
            continue;
        }
    IoWriteSingleLut:
        word Truth = Abc_SopToTruth( (char *)pObj->pData, Abc_ObjFaninNum(pObj) );
        fprintf( pFile, "  lut%d #(%d\'h", nLutSize, 1<<nLutSize );
        if ( nLutSize == 6 )
            fprintf( pFile, "%08x%08x", (unsigned)(Truth >> 32), (unsigned)Truth );
        else
            fprintf( pFile, "%0*x", 1<<(nLutSize-2), Abc_InfoMask(1 << nLutSize) & (unsigned)Truth );
        fprintf( pFile, ") lut_%0*d ( {", nDigits, Counter++ );
        for ( k = nLutSize - 1; k >= Abc_ObjFaninNum(pObj); k-- )
            fprintf( pFile, "%*s, ", Length, "1\'b0" );
        for ( k = Abc_ObjFaninNum(pObj) - 1; k >= 0; k-- )
            fprintf( pFile, "%*s%s", Length, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanin(pObj, k))), k==0 ? "":", " );
        fprintf( pFile, "}, %*s );\n", Length, Io_WriteVerilogGetName(Abc_ObjName(Abc_ObjFanout0(pObj))) );
        Vec_IntWriteEntry( vPrinted, pObj->Id, 1 );
    }
    Vec_IntFree( vPrinted );
    }
}
void Io_WriteVerilogLutInt( FILE * pFile, Abc_Ntk_t * pNtk, int nLutSize, int fFixed, int fNewInterface )
{
    // write inputs and outputs
//    fprintf( pFile, "module %s ( gclk,\n   ", Abc_NtkName(pNtk) );
    fprintf( pFile, "module %s ( ", Io_WriteVerilogGetName(Abc_NtkName(pNtk)) );
    // add the clock signal if it does not exist
    if ( Abc_NtkLatchNum(pNtk) > 0 && Nm_ManFindIdByName(pNtk->pManName, "clock", ABC_OBJ_PI) == -1 )
        fprintf( pFile, "clock, " );
    // write other primary inputs
    fprintf( pFile, "\n   " );
    if ( Abc_NtkPiNum(pNtk) > 0  )
    {
        Io_WriteVerilogPis( pFile, pNtk, 3 );
        fprintf( pFile, ",\n   " );
    }
    if ( Abc_NtkPoNum(pNtk) > 0  )
        Io_WriteVerilogPos( pFile, pNtk, 3, fNewInterface );
    fprintf( pFile, "  );\n\n" );
    // add the clock signal if it does not exist
    if ( Abc_NtkLatchNum(pNtk) > 0 && Nm_ManFindIdByName(pNtk->pManName, "clock", ABC_OBJ_PI) == -1 )
        fprintf( pFile, "  input  clock;\n" );
    // write inputs, outputs, registers, and wires
    if ( Abc_NtkPiNum(pNtk) > 0  )
    {
//        fprintf( pFile, "  input gclk," );
        fprintf( pFile, "  input " );
        Io_WriteVerilogPis( pFile, pNtk, 10 );
        fprintf( pFile, ";\n" );
    }
    if ( Abc_NtkPoNum(pNtk) > 0  )
    {
        fprintf( pFile, "  output" );
        Io_WriteVerilogPos( pFile, pNtk, 5, fNewInterface );
        fprintf( pFile, ";\n\n" );
    }
    // if this is not a blackbox, write internal signals
    if ( !Abc_NtkHasBlackbox(pNtk) )
    {
        if ( Abc_NtkLatchNum(pNtk) > 0 )
        {
            fprintf( pFile, "  reg" );
            Io_WriteVerilogRegs( pFile, pNtk, 4 );
            fprintf( pFile, ";\n\n" );
        }
        if ( Io_WriteVerilogWiresCount(pNtk) > 0 )
        {
            fprintf( pFile, "  wire" );
            Io_WriteVerilogWires( pFile, pNtk, 4 );
            fprintf( pFile, ";\n\n" );
        }
        // write nodes
        Io_WriteVerilogObjectsLut( pFile, pNtk, nLutSize, fFixed );        
        // write registers
        if ( Abc_NtkLatchNum(pNtk) > 0 )
        {
            fprintf( pFile, "\n" );
            Io_WriteVerilogLatches( pFile, pNtk );
        }
    }
    if ( fNewInterface )
        Io_WriteVerilogAssigns( pFile, pNtk );
    // finalize the file
    fprintf( pFile, "\nendmodule\n\n" );
} 
void Io_WriteVerilogLut( Abc_Ntk_t * pNtk, char * pFileName, int nLutSize, int fFixed, int fNoModules, int fNewInterface )
{
    FILE * pFile;
    Abc_Ntk_t * pNtkTemp;
    Abc_Obj_t * pObj; 
    int i, Counter = 0;
    Abc_NtkForEachNode( pNtk, pObj, i )
        if ( Abc_ObjFaninNum(pObj) > nLutSize )
        {
            if ( Counter < 3 )
                printf( "Node \"%s\" has the fanin count (%d) larger than the LUT size (%d).\n", Abc_ObjName(pObj), Abc_ObjFaninNum(pObj), nLutSize );
            Counter++;
        }
    if ( Counter )
    {
        printf( "In total, %d internal logic nodes exceed the fanin count limit. Verilog is not written.\n", Counter );
        return;
    }

    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteVerilog(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    // write the equations for the network
    fprintf( pFile, "// Benchmark \"%s\" written by ABC on %s\n", pNtk->pName, Extra_TimeStamp() );
    fprintf( pFile, "\n" );
    if ( !fNoModules )
    {
        if ( fFixed )
            Io_WriteFixedModules( pFile );
        else
            Io_WriteLutModule( pFile, nLutSize );
        if ( Io_WriteVerilogLutHasDualAttrs(pNtk) )
            Io_WriteDualLutModule( pFile, nLutSize );
    }
    pNtkTemp = Abc_NtkToNetlist( pNtk );
    Abc_NtkToSop( pNtkTemp, -1, ABC_INFINITY );
    Io_WriteVerilogLutTransferDualAttrs( pNtk, pNtkTemp );
    Io_WriteVerilogLutInt( pFile, pNtkTemp, nLutSize, fFixed, fNewInterface );
    Abc_NtkDelete( pNtkTemp );

    fprintf( pFile, "\n" );
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
