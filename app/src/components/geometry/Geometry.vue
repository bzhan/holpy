<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">geometry</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#">New</b-dropdown-item>
          <b-dropdown-item href="#">Open</b-dropdown-item>
          <b-dropdown-item href="#">Save</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item href="#" @click="handleClickSelect">Select</b-nav-item>
        <b-nav-item-dropdown text="Construct" left>
          <b-dropdown-item href="#" @click="handleClickConstructPoint">Point</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructLine">Line</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructCircle">Circle</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Constraint" left>
          <b-dropdown-item href="#">Equal Angle</b-dropdown-item>
          <b-dropdown-item href="#">Equal Ratio</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Prove" left>
          <b-dropdown-item href="#">Prove</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Help" left>
          <b-dropdown-item href='#'>Help</b-dropdown-item>
        </b-nav-item-dropdown>        
      </b-navbar-nav>
    </b-navbar>
    <div id="canvas" ref="p">
      <v-stage :config="stageSize" ref="stage" @click="handleClickLayer">
        <v-layer id="lineLayer" ref="lineLayer"></v-layer>
        <v-layer id="anchorLayer" ref="anchorLayer"></v-layer>

      </v-stage>
    </div>
    <div id="tool">
      <h6>{{status}}</h6>
    </div>

<!--    <div id="theory-list" v-show="ref_proof === undefined">-->
<!--      <Content v-if="filelist !== undefined"-->
<!--               v-bind:filelist="filelist"-->
<!--               v-on:select-theory="onSelectTheory"-->
<!--               ref="content"/>-->
<!--    </div>-->
<!--    <div id="proof-context" v-show="ref_proof !== undefined">-->
<!--      <ProofContext v-bind:ref_proof="ref_proof" ref="context"/>-->
<!--    </div>-->
<!--    <div id="theory-content">-->
<!--      <Theory v-bind:theory="theory"-->
<!--              v-bind:ref_status="ref_status"-->
<!--              v-bind:ref_context="ref_context"-->
<!--              :editor="editor"-->
<!--              v-on:set-message="onSetMessage"-->
<!--              v-on:set-proof="handle_set_proof"-->
<!--              v-on:query="handle_query"-->
<!--              v-on:goto-link="handleGoToLink"-->
<!--              ref="theory"/>-->
<!--    </div>-->
<!--    <div id="message" v-show="ref_proof === undefined">-->
<!--      <Message v-bind:message="message" ref="message"/>-->
<!--    </div>-->
<!--    <div id="status" v-show="ref_proof !== undefined && query === undefined">-->
<!--      <ProofStatus v-bind:ref_proof="ref_proof" ref="status"/>-->
<!--    </div>-->
<!--    <div id="query" v-show="ref_proof !== undefined && query !== undefined">-->
<!--      <ProofQuery v-bind:query="query"-->
<!--                  v-on:query-ok="handle_query_ok"-->
<!--                  v-on:query-cancel="handle_query_cancel"/>-->
<!--    </div>-->

  </div>
</template>

<script>
  import Vue from 'vue'
  import VueKonva from 'vue-konva'
  import Konva from 'konva'
  Vue.use(VueKonva)
  Vue.use(Konva)
  export default {
    name: 'Geometry',
    components: {
    },
    data() {
      return {
        stageSize: {
          width: null,
          height: null,
        },
        status: "select",
        points: [],
        lines: [],
        selected: []
      }
    },
    mounted() {
      this.matchSize()
    },
    created: function() {
      window.addEventListener("resize", this.matchSize)
    },
    methods: {
      matchSize() {
        this.stageSize.height = this.$refs.p.clientHeight - 10
        this.stageSize.width = this.$refs.p.clientWidth - 10
      },
      handleClickLayer() {
        const x = this.$refs.stage.getNode().getPointerPosition().x
        const y = this.$refs.stage.getNode().getPointerPosition().y
        if (this.status === "point") {
          this.addAnchor(x, y)
        }
      },
      checkHaveName(name) {
        for (let id in this.points) {
          if (name === this.points[id]['name']) {
            return true
          }
        }
        return false
      },
      parseIdToName(id) {
        if (parseInt(id / 26) === 0) {
          return String.fromCharCode(65 + id % 26)
        }
        else {
          return String.fromCharCode(65 + id % 26) + String(parseInt(id / 26))
        }
      },
      addLine(id1, id2) {
        const anchor1 = this.$refs.stage.getNode().find('#' + id1)[0].getChildren()[0]
        const anchor2 = this.$refs.stage.getNode().find('#' + id2)[0].getChildren()[0]
        const pos1 = anchor1.getAbsolutePosition()
        const pos2 = anchor2.getAbsolutePosition()
        let id = 100
        while (this.lines.hasOwnProperty(id)) {
          id += 1
        }
        this.lines[id] = {"children": [id1, id2], "activated": false}
        const newLine = new Konva.Line({
          points: [pos1['x'], pos1['y'], pos2['x'], pos2['y']],
          stroke: "black",
          strokeWidth: 2,
          id: id
        })
        newLine.on("mouseover", this.handleMouseOver)
        newLine.on("mouseout", this.handleMouseOut)
        newLine.on("click", this.handleClickLine)
        this.$refs.lineLayer.getNode().add(newLine)
        this.$refs.lineLayer.getNode().draw()
      },
      addAnchor(x, y) {
        let id = 0
        while (this.points.hasOwnProperty(id)) {
          id += 1
        }
        let name = this.parseIdToName(id)
        let t_id = id
        while (this.checkHaveName(name)) {
          t_id += 1
          name = this.parseIdToName(t_id)
        }
        this.points[id] = {"name": name, "activated": false}
        const group = new Konva.Group({
          draggable: true,
          isDragging: false,
          id: id.toString()
        });
        const newShape = new Konva.Circle({
          x: x,
          y: y,
          radius: 5,
          stroke: "black",
          strokeWidth: 2,
          fill: "red",
        })
        const newText = new Konva.Text({
          x: x + 5,
          y: y - 20,
          text: name,
          fontSize: 16
        })
        group.add(newShape)
        group.add(newText)
        group.on("mouseover", this.handleMouseOver)
        group.on("mouseout", this.handleMouseOut)
        group.on("click", this.handleClickAnchor)
        group.on("dragstart", this.handleDragStartAnchor)
        group.on("dragend", this.handleDragEndAnchor)
        this.$refs.anchorLayer.getNode().add(group)
        this.$refs.anchorLayer.getNode().draw()
      },
      handleMouseOver(e) {
        document.body.style.cursor = 'pointer'
        e.target.strokeWidth(4)
        this.$refs.anchorLayer.getNode().draw()
        this.$refs.lineLayer.getNode().draw()
      },
      handleMouseOut(e) {
        document.body.style.cursor = 'default'
        if (e.target.constructor.name === 'Circle') {
          const id = e.target.getParent().getAttr('id')
          if (this.points[id]["activated"] === false) {
            e.target.strokeWidth(2)
            this.$refs.anchorLayer.getNode().draw()
          }
        }
        else if (e.target.constructor.name === 'Line') {
          const id = e.target.getAttr('id')
          if (this.lines[id]["activated"] === false) {
            e.target.strokeWidth(2)
            this.$refs.lineLayer.getNode().draw()
          }
        }
      },
      handleClickLine(e) {
        if (this.status === "select") {
          this.toggleActivationLine(e)
        }
      },
      handleClickAnchor(e) {
        if (this.status === "select") {
          this.toggleActivationAnchor(e)
        }
        else if (this.status === "line") {
          this.toggleActivationOn(e, e.target.getParent().index, this.points)
          if (this.selected.length < 1) {
            this.addAnchorToSelected(e.target.getParent().index)
          } else {
            this.addAnchorToSelected(e.target.getParent().index)
            this.addLine(this.selected[0], this.selected[1])
            this.selected = []
            this.clearAnchorsActivation()
          }
        }
      },
      addAnchorToSelected(id) {
        this.selected.push(id)
      },
      handleDragStartAnchor() {
      },
      handleDragMoveAnchor() {
        // this.updateLine()
      },
      handleDragEndAnchor() {
      },
      handleClickSelect() {
        this.status = "select"
      },
      handleClickConstructPoint() {
        this.status = "point"
      },
      handleClickConstructLine() {
        this.status = "line"
      },
      handleClickConstructCircle() {
        this.status = "circle"
      },
      updateLine() {
      },
      toggleActivationOn(e, id, entry) {
        entry[id]["activated"] = true
        e.target.strokeWidth(4)
      },
      toggleActivationOff(e, id, entry) {
        entry[id]["activated"] = false
        e.target.strokeWidth(2)
      },
      toggleActivation(e, id, entry) {
        if (entry[id]["activated"] === true) {
          this.toggleActivationOff(e, id, entry)
        } else {
          this.toggleActivationOn(e, id, entry)
        }
      },
      toggleActivationAnchor(e) {
        const id = e.target.getParent().getAttr('id')
        this.toggleActivation(e, id, this.points)
        this.$refs.anchorLayer.getNode().draw()
      },
      toggleActivationLine(e) {
        const id = e.target.getAttr('id')
        window.console.log(id)
        this.toggleActivation(e, id, this.lines)
        this.$refs.lineLayer.getNode().draw()
      },
      clearAnchorsActivation() {
        let children = this.$refs.anchorLayer.getNode().getChildren()
        for (let i = 0; i < children.length; i ++) {
          children[i].getChildren()[0].strokeWidth(2)
        }
        this.$refs.anchorLayer.getNode().draw()
        for (let id in this.points) {
          this.points[id]['activated'] = false
        }
      }
    },
    watch: {
      status() {
        this.clearAnchorsActivation()
      }
    }
  }
</script>

<style scoped>

/*Disable blank scrollbar in Chrome. */
/*::-webkit-scrollbar {*/
/*  width: 0 !important;height: 0;}*/

#canvas {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#theory-list, #proof-context {
  display: inline-block;
  width: 25%;
  position: fixed;
  top: 48px;
  bottom: 0;
  left: 0;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 5px;
}

#theory-content {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#message, #status, #query {
  display: inline-block;
  width: 75%;
  height: 25%;
  left: 25%;
  position: fixed;
  top: 75%;
  bottom: 0;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

#tool {
  display: inline-block;
  width: 75%;
  height: 5%;
  left: 25%;
  position: fixed;
  top: 70%;
  bottom: 0;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

</style>